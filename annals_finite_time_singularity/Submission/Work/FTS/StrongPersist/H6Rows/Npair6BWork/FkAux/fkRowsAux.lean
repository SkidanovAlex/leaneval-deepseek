import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FKstarSlotPiece
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.radialMatchedMajorant
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.slotEnergyLeHkSq
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SlotPairingHkSq
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.supDz_zslice6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaEnd
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkThetaAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.FKdzIter_sq_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkArith
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

/-- **Monotonicity of the `ℋᵏ`-integrand in the level.**  Every slot occurring at level `m`
also occurs at level `m' ≥ m` (the sums run over larger ranges and the guard
`1 ≤ i ∧ i + j ≤ m` is weaker at `m'`), so the integrand increases. -/
theorem HkIntegrand_mono {α : ℝ} {m m' : ℕ} (h : m ≤ m') (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α m g z θ ≤ Work.Spaces.HkIntegrand α m' g z θ := by
  unfold Work.Spaces.HkIntegrand
  have hpure : (∑ i ∈ Finset.range (m + 1), (Work.Spaces.DzIter i g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ (∑ i ∈ Finset.range (m' + 1), (Work.Spaces.DzIter i g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
      (fun i _ _ => sq_nonneg _)
  have hterm : ∀ i j : ℕ,
      (if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0)
      ≤ (if 1 ≤ i ∧ i + j ≤ m' then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0) := by
    intro i j
    by_cases hc : 1 ≤ i ∧ i + j ≤ m
    · rw [if_pos hc, if_pos ⟨hc.1, by omega⟩]
    · rw [if_neg hc]
      split_ifs with hp
      · exact sq_nonneg _
      · exact le_rfl
  have hin : ∀ i : ℕ,
      (∑ j ∈ Finset.range (m + 1), (if 1 ≤ i ∧ i + j ≤ m then
          (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ (∑ j ∈ Finset.range (m' + 1), (if 1 ≤ i ∧ i + j ≤ m' then
          (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
    intro i
    refine le_trans (Finset.sum_le_sum fun j _ => hterm i j) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) ?_
    intro j _ _
    split_ifs with hp
    · exact sq_nonneg _
    · exact le_rfl
  have hmix : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (if 1 ≤ i ∧ i + j ≤ m then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0))
      ≤ (∑ i ∈ Finset.range (m' + 1), ∑ j ∈ Finset.range (m' + 1),
        (if 1 ≤ i ∧ i + j ≤ m' then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)) := by
    refine le_trans (Finset.sum_le_sum fun i _ => hin i) ?_
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega)) ?_
    intro i _ _
    refine Finset.sum_nonneg fun j _ => ?_
    split_ifs with hp
    · exact sq_nonneg _
    · exact le_rfl
  exact add_le_add hpure hmix

/-! ## Elementary helper lemmas -/

/-- **Monotonicity of `HkSq` in the level** (from the pointwise monotonicity of the integrand). -/
theorem HkSq_mono {α : ℝ} {m m' : ℕ} (h : m ≤ m') {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α m' g) : Work.Spaces.HkSq α m g ≤ Work.Spaces.HkSq α m' g := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m g z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m' g z θ := by
    intro z hz
    refine Work.Spaces.integral_le_integral_of_ae_le_of_nonneg (hmem.1 z hz)
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α m' g z θ) ?_
    exact Filter.Eventually.of_forall fun θ => HkIntegrand_mono h g z θ
  rw [Work.Spaces.HkSq]
  exact Work.Spaces.integral_le_integral_of_ae_le_of_nonneg hmem.2
    (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α m' g z θ)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hinner)

/-- `D_θ`-iterates add: `D_θ^{a+b} = D_θ^a ∘ D_θ^b`. -/
theorem DthIter_add (a b : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter (a + b) f = Work.Spaces.DthIter a (Work.Spaces.DthIter b f) := by
  induction a with
  | zero => simp
  | succ a ih =>
      simp only [Nat.succ_add, Work.Spaces.DthIter_succ, ih]

/-- `D_θ^j` of `D_θf` is `D_θ^{j+1}f`, i.e. `mixed b j (D_θf) = mixed b (j+1) f`. -/
theorem mixed_Dth_one (j i : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (Work.Spaces.Dth f) = Work.Spaces.mixed j (i + 1) f := by
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dth f))
    = Work.Spaces.DzIter j (Work.Spaces.DthIter (i + 1) f)
  rw [show Work.Spaces.Dth f = Work.Spaces.DthIter 1 f from rfl, ← DthIter_add i 1]

/-- `HkSq α m g ≤ HkSq α 6 g` for `m ≤ 6`. -/
theorem HkSq_le_S {α : ℝ} {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 6 g)
    {m : ℕ} (hm : m ≤ 6) : Work.Spaces.HkSq α m g ≤ Work.Spaces.HkSq α 6 g :=
  HkSq_mono hm hmem

/-- **The `ℋ⁴`-norm bound in terms of `M`.**  `Xn α f = √(HkSq α 4 f)` is definitionally
`HkNorm α 4 f`, so `Xn α f ≤ M` gives `HkSq α m f ≤ M^2` for every `m ≤ 4`. -/
theorem HkSq_le_Msq {α : ℝ} {f : ℝ → ℝ → ℝ} {M : ℝ}
    (hM : Work.FTS.Nonlin.Xn α f ≤ M) (hmem4 : Work.Spaces.HkMem α 4 f)
    {m : ℕ} (hm : m ≤ 4) : Work.Spaces.HkSq α m f ≤ M ^ 2 := by
  have h4 : Work.Spaces.HkSq α 4 f = (Work.FTS.Nonlin.Xn α f) ^ 2 := by
    show Work.Spaces.HkSq α 4 f = (Work.Spaces.HkNorm α 4 f) ^ 2
    rw [Work.Spaces.HkNorm]
    exact (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)).symm
  have hXn0 : 0 ≤ Work.FTS.Nonlin.Xn α f := Real.sqrt_nonneg _
  have hM0 : 0 ≤ M := le_trans hXn0 hM
  calc Work.Spaces.HkSq α m f ≤ Work.Spaces.HkSq α 4 f := HkSq_mono hm hmem4
    _ = (Work.FTS.Nonlin.Xn α f) ^ 2 := h4
    _ ≤ M ^ 2 := by nlinarith [hXn0, hM]

/-- `1 ≤ α ^ (-(3:ℝ))` for `α ∈ (0,1]`. -/
theorem one_le_alpha_rpow {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) ≤ α ^ (-(3 : ℝ)) := by
  rw [Real.rpow_neg hα.le]
  have h1 : α ^ (3 : ℝ) ≤ 1 := Real.rpow_le_one hα.le hα1 (by norm_num)
  have h2 : 0 < α ^ (3 : ℝ) := Real.rpow_pos_of_pos hα _
  rw [one_le_inv₀ h2]
  exact h1

/-- **The radial Leibniz rule for `mixed j i (r · g)`**, uniformly in `i = 0` and `i ≥ 1`:
the `θ`-derivatives all fall on `g` (the radial factor `r` is `θ`-free). -/
theorem leibniz_rad_any {r : ℝ → ℝ} {g : ℝ → ℝ → ℝ}
    (hr : ContDiffOn ℝ 6 (Function.uncurry (fun z (_ : ℝ) => r z)) Work.FTS.EllipticEst.Q0)
    (hg : ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0)
    {j i : ℕ} (hij : i + j ≤ 6) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed j i (fun z θ => r z * g z θ) z θ
        = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
            * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i g z θ) := by
  intro z θ hz hθ hθ2
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    have h := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_Dz_cd6
      (r := r) (g := g) hr hg (j := j) (by omega) z θ hz hθ hθ2
    rw [Work.Spaces.mixed_zero_right, h]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Work.Spaces.mixed_zero_right]
  · exact Work.FTS.StrongPersist.H6Rows.Npair6SupAux.RadAux.leibniz_rad_mixed_cd6
      (r := r) (g := g) hr hg hipos hij z θ hz hθ hθ2

/-- The `θ`-integral of a finite sum with `z`-only coefficients. -/
theorem integral_sum_coeff_finset {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    {g : ι → ℝ → ℝ} {z : ℝ} (hg : ∀ i ∈ s, MeasureTheory.Integrable (g i)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    (∫ θ in Work.Spaces.Iθ, ∑ i ∈ s, c i * g i θ) = ∑ i ∈ s, c i * ∫ θ in Work.Spaces.Iθ, g i θ := by
  rw [MeasureTheory.integral_finset_sum _ (fun i hi => (hg i hi).const_mul _)]
  exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _

/-- **The pointwise `AM–GM`/Cauchy–Schwarz bound for the radial Leibniz expansion.**  Together
with the pointwise pricing of the individual slots this dominates the pairing integrand by a
constant multiple of a sum of `HkIntegrand` slots. -/
theorem mixed_radial_mul_le {r : ℝ → ℝ} {X X' V : ℝ → ℝ → ℝ} {a A b : ℕ} {ρ : ℝ → ℝ → ℝ}
    {z θ : ℝ} (hρ : 0 ≤ ρ z θ) {Cb : ℕ → ℝ}
    (hDz : Work.Spaces.mixed b a (fun z θ => r z * X z θ) z θ
      = ∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ)
          * (Work.Elliptic.DzdIter b₁ r z * Work.Spaces.mixed (b - b₁) A X' z θ))
    (hCb : ∀ b₁ ∈ Finset.range (b + 1), (Work.Elliptic.DzdIter b₁ r z) ^ 2 ≤ Cb b₁) :
    ρ z θ * |Work.Spaces.mixed b a (fun z θ => r z * X z θ) z θ| * |V z θ|
      ≤ ((b : ℝ) + 1) * (∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ) ^ 2 * Cb b₁
            * (ρ z θ * (Work.Spaces.mixed (b - b₁) A X' z θ) ^ 2)) / 2
          + ρ z θ * (V z θ) ^ 2 / 2 := by
  have hcs : (∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ)
        * (Work.Elliptic.DzdIter b₁ r z * Work.Spaces.mixed (b - b₁) A X' z θ)) ^ 2
      ≤ ((b : ℝ) + 1) * ∑ b₁ ∈ Finset.range (b + 1), ((b.choose b₁ : ℝ)
        * (Work.Elliptic.DzdIter b₁ r z
            * Work.Spaces.mixed (b - b₁) A X' z θ)) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (b + 1)) (fun _ : ℕ => (1 : ℝ))
      (fun b₁ => (b.choose b₁ : ℝ)
        * (Work.Elliptic.DzdIter b₁ r z * Work.Spaces.mixed (b - b₁) A X' z θ))
    have hcard : (∑ _i ∈ Finset.range (b + 1), (1 : ℝ)) = (b : ℝ) + 1 := by
      have hgen : ∀ n : ℕ, (∑ _i ∈ Finset.range n, (1 : ℝ)) = (n : ℝ) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
      rw [hgen (b + 1)]
      push_cast
      ring
    simpa only [one_mul, one_pow, hcard] using h
  have hper : ∑ b₁ ∈ Finset.range (b + 1), ((b.choose b₁ : ℝ)
        * (Work.Elliptic.DzdIter b₁ r z * Work.Spaces.mixed (b - b₁) A X' z θ)) ^ 2
      ≤ ∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ) ^ 2 * Cb b₁
          * (Work.Spaces.mixed (b - b₁) A X' z θ) ^ 2 := by
    refine Finset.sum_le_sum fun b₁ hb₁ => ?_
    calc ((b.choose b₁ : ℝ)
          * (Work.Elliptic.DzdIter b₁ r z * Work.Spaces.mixed (b - b₁) A X' z θ)) ^ 2
        = ((b.choose b₁ : ℝ) ^ 2 * (Work.Spaces.mixed (b - b₁) A X' z θ) ^ 2)
            * (Work.Elliptic.DzdIter b₁ r z) ^ 2 := by ring
      _ ≤ ((b.choose b₁ : ℝ) ^ 2 * (Work.Spaces.mixed (b - b₁) A X' z θ) ^ 2) * Cb b₁ :=
          mul_le_mul_of_nonneg_left (hCb b₁ hb₁) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      _ = (b.choose b₁ : ℝ) ^ 2 * Cb b₁ * (Work.Spaces.mixed (b - b₁) A X' z θ) ^ 2 := by ring
  have hmixed : (Work.Spaces.mixed b a (fun z θ => r z * X z θ) z θ) ^ 2
      ≤ ((b : ℝ) + 1) * ∑ b₁ ∈ Finset.range (b + 1),
          (b.choose b₁ : ℝ) ^ 2 * Cb b₁ * (Work.Spaces.mixed (b - b₁) A X' z θ) ^ 2 := by
    rw [hDz]
    exact le_trans hcs (mul_le_mul_of_nonneg_left hper (by positivity))
  have hmixed' : ρ z θ * (Work.Spaces.mixed b a (fun z θ => r z * X z θ) z θ) ^ 2
      ≤ ((b : ℝ) + 1) * (∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ) ^ 2 * Cb b₁
            * (ρ z θ * (Work.Spaces.mixed (b - b₁) A X' z θ) ^ 2)) := by
    have h := mul_le_mul_of_nonneg_left hmixed hρ
    have h2 : ρ z θ * (∑ b₁ ∈ Finset.range (b + 1),
          (b.choose b₁ : ℝ) ^ 2 * Cb b₁ * (Work.Spaces.mixed (b - b₁) A X' z θ) ^ 2)
        = ∑ b₁ ∈ Finset.range (b + 1), ρ z θ
            * ((b.choose b₁ : ℝ) ^ 2 * Cb b₁ * (Work.Spaces.mixed (b - b₁) A X' z θ) ^ 2) := by
      rw [Finset.mul_sum]
    have h3 : ∑ b₁ ∈ Finset.range (b + 1), ρ z θ
          * ((b.choose b₁ : ℝ) ^ 2 * Cb b₁ * (Work.Spaces.mixed (b - b₁) A X' z θ) ^ 2)
        = ∑ b₁ ∈ Finset.range (b + 1), (b.choose b₁ : ℝ) ^ 2 * Cb b₁
            * (ρ z θ * (Work.Spaces.mixed (b - b₁) A X' z θ) ^ 2) := by
      refine Finset.sum_congr rfl fun b₁ _ => by ring
    have h1 : ρ z θ * (((b : ℝ) + 1) * (∑ b₁ ∈ Finset.range (b + 1),
          (b.choose b₁ : ℝ) ^ 2 * Cb b₁ * (Work.Spaces.mixed (b - b₁) A X' z θ) ^ 2))
        = ((b : ℝ) + 1) * (ρ z θ * (∑ b₁ ∈ Finset.range (b + 1),
          (b.choose b₁ : ℝ) ^ 2 * Cb b₁ * (Work.Spaces.mixed (b - b₁) A X' z θ) ^ 2)) := by ring
    rw [h1, h2, h3] at h
    exact h
  have hAM : ρ z θ * |Work.Spaces.mixed b a (fun z θ => r z * X z θ) z θ| * |V z θ|
      ≤ (ρ z θ * (Work.Spaces.mixed b a (fun z θ => r z * X z θ) z θ) ^ 2
          + ρ z θ * (V z θ) ^ 2) / 2 := by
    have h2 := Work.Spaces.abs_mul_abs_le_half_add_sq
      (Work.Spaces.mixed b a (fun z θ => r z * X z θ) z θ) (V z θ)
    calc ρ z θ * |Work.Spaces.mixed b a (fun z θ => r z * X z θ) z θ| * |V z θ|
        = ρ z θ * (|Work.Spaces.mixed b a (fun z θ => r z * X z θ) z θ| * |V z θ|) := by ring
      _ ≤ ρ z θ * (((Work.Spaces.mixed b a (fun z θ => r z * X z θ) z θ) ^ 2
            + (V z θ) ^ 2) / 2) := mul_le_mul_of_nonneg_left h2 hρ
      _ = (ρ z θ * (Work.Spaces.mixed b a (fun z θ => r z * X z θ) z θ) ^ 2
            + ρ z θ * (V z θ) ^ 2) / 2 := by ring
  linarith [hAM, hmixed']

/-- **The absolute-value pairing bound.**  For a leaf weight `ρ` that is nonnegative on `Iθ`,
the slot pairing is dominated by the iterated integral of `ρ|U||V|` (the latter being assumed
integrable so that the totalised integral of the dominator is honest). -/
theorem slotPairing_abs_le {ρ U V : ℝ → ℝ → ℝ} (a b : ℕ)
    (hρ : ∀ z θ, θ ∈ Work.Spaces.Iθ → 0 ≤ ρ z θ)
    (hInt : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * |Work.Spaces.mixed b a U z θ|
        * |Work.Spaces.mixed b a V z θ|) Work.Spaces.Iz) :
    |Work.FTS.TransportS.slotPairing ρ a b U V|
      ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ
          * |Work.Spaces.mixed b a U z θ| * |Work.Spaces.mixed b a V z θ| := by
  rw [Work.FTS.TransportS.slotPairing]
  refine le_trans (MeasureTheory.abs_integral_le_integral_abs) ?_
  refine Work.Spaces.integral_le_integral_of_ae_le_of_nonneg hInt
    (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
        mul_nonneg (mul_nonneg (hρ z θ hθ) (abs_nonneg _)) (abs_nonneg _))) ?_
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z _ => ?_
    refine le_trans (MeasureTheory.abs_integral_le_integral_abs) (le_of_eq ?_)
    exact MeasureTheory.integral_congr_ae
      ((MeasureTheory.ae_restrict_mem measurableSet_Icc).mono fun θ hθ => by
        show |ρ z θ * Work.Spaces.mixed b a U z θ * Work.Spaces.mixed b a V z θ|
            = ρ z θ * |Work.Spaces.mixed b a U z θ| * |Work.Spaces.mixed b a V z θ|
        rw [abs_mul, abs_mul, abs_of_nonneg (hρ z θ hθ)])

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
