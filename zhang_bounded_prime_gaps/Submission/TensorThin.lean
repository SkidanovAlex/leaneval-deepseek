import Mathlib
import Submission.TensorConvergence
import Submission.SieveMargKey
import Submission.Commons.Analysis.Integral.abs_integral_Ioi_le_thin

open scoped BigOperators Topology
open Filter Finset MeasureTheory

set_option maxHeartbeats 2000000

/-!
# The thin tensor data of §5.3

`exists_tensorData_near` (`Submission/TensorConvergence.lean`) now builds its tensor data from the
*thin* localisation `Commons.Analysis.TensorApprox.exists_tensor_localization_orthant_thin` and
exports, besides the `tpAlpha`/`tpBeta` approximations,

* the thin support structure `0 ≤ u → G j i u ≠ 0 → β j i - 6η < u ∧ u < β j i`,
* a uniform bound `B` for the components and for `Σ_j |c j| ∏_i |G j i (t i)|`,
* the tensor sum `Gtf`, its coordinate bound `Bg = R + 12kη`, its uniform distance `el` from `F`,
  the bound `CF` for `|F|`, and the resulting marginal-comparison error bound
  `el·Bg·(2·CF·Bg + el·Bg)·Bg^{k-1} ≤ δ/2`.

This module converts the last item into the radius-`cc` marginal comparison
`|J̃_i - JFunc k i cc F| ≤ δ/2` (via `margTensor_near_JFunc`), which is exactly the input
`hJapprox` of `hkey_of_split_tensorData`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- **The thin tensor data with the radius-`cc` marginal comparison.** -/
theorem exists_tensorData_thin {k : ℕ} {F : (Fin k → ℝ) → ℝ} (hFc : Continuous F)
    (hFcs : HasCompactSupport F) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ t, F t ≠ 0 → (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ R)
    (hk : 1 ≤ k) {η δ cc M : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (h1 : R + 24 * (k : ℝ) * η ≤ 1) (hM : ∀ t : Fin k → ℝ, |F t| ≤ M) :
    ∃ (ψ : ℝ → ℝ) (J : ℕ) (Gt : Fin J → Fin k → ℝ → ℝ) (c : Fin J → ℝ)
      (β : Fin J → Fin k → ℝ),
      ψ 0 = 1 ∧ (∀ u : ℝ, 0 ≤ u → ψ u = 1) ∧
      (∀ j i, ContDiff ℝ (↑(⊤ : ℕ∞)) (Gt j i)) ∧
      (∀ j i, HasCompactSupport (Gt j i)) ∧
      (∀ j i, 0 ≤ β j i) ∧
      (∀ j i u, 0 ≤ u → Gt j i u ≠ 0 → β j i - 6 * η < u ∧ u < β j i) ∧
      (∀ j i u, β j i < u → Gt j i u = 0) ∧
      (∀ j i, β j i ≤ R + 12 * (k : ℝ) * η) ∧
      (∀ j, ∑ i, β j i ≤ R + 12 * (k : ℝ) * η) ∧
      (∃ B : ℝ, 0 ≤ B ∧ (∀ j i u, |Gt j i u| ≤ B) ∧
        (∀ t : Fin k → ℝ, ∑ j, |c j| * ∏ i, |Gt j i (t i)| ≤ B)) ∧
      0 ≤ M ∧
      (∀ (i₀ : Fin k) (t : {l : Fin k // l ≠ i₀} → ℝ),
        ∑ j, |c j| * ∏ l : {l : Fin k // l ≠ i₀}, |Gt j (l : Fin k) (t l)| ≤ M) ∧
      |tpAlpha c (fun j i => anti ψ (Gt j) i) - IFuncOrth k F| < δ ∧
      (∀ i₀ : Fin k, |(∫ t : ({l : Fin k // l ≠ i₀} → ℝ),
          (tenP Gt c i₀ Finset.univ t) ^ 2 * margInd k i₀ cc t) - JFunc k i₀ cc F|
        ≤ δ / 2) := by
  classical
  obtain ⟨ψ, hψsm, hψ0', hψ1', hψ01⟩ :=
    Commons.Analysis.Calculus.exists_contDiff_step (-(12 * η)) 0 (by linarith)
  have hψ0 : ψ 0 = 1 := hψ1' 0 le_rfl
  have hψ1 : ∀ u : ℝ, 0 ≤ u → ψ u = 1 := fun u hu => hψ1' u hu
  obtain ⟨J, β, Gt, c, hGtsm, hGtcs, hGtvan, hβnn, hβind, hβsum, hthin, hBdata, hJnear,
      hαnear, hβnear, _hBmargdata⟩ :=
    exists_tensorData_near hFc hFcs hR0 hR hψ0 hψ1 hη hδ hM
  obtain ⟨B, hB0, hBbd, hBsum⟩ := hBdata
  obtain ⟨Gtf, Bg, el, CF, hGtf_eq, hBg, hel, hCF0, hCF, hGcoord, happrox, hfullM, hmargM,
    hbound⟩ := hJnear
  have hM0 : (0:ℝ) ≤ M := le_trans (abs_nonneg (F (fun _ => 0))) (hM (fun _ => 0))
  refine ⟨ψ, J, Gt, c, β, hψ0, hψ1, hGtsm, hGtcs, hβnn, hthin, hGtvan, hβind, hβsum,
    ⟨B, hB0, hBbd, hBsum⟩, hM0, (fun i₀ t => hmargM i₀ t), hαnear, ?_⟩
  -- the radius-`cc` marginal comparison
  have hBg0 : 0 ≤ Bg := by rw [hBg]; positivity
  have hRB : R ≤ Bg := by rw [hBg]; nlinarith [hη, Nat.cast_nonneg (α := ℝ) k]
  have hF0 : ∀ s : Fin k → ℝ, F s ≠ 0 → ∀ i, 0 ≤ s i := fun s hs => (hR s hs).1
  have hFcoord : ∀ s : Fin k → ℝ, (∃ i, R < s i) → F s = 0 := by
    intro s hs
    by_contra hne
    obtain ⟨hnn, hle⟩ := hR s hne
    obtain ⟨i, hi⟩ := hs
    have : s i ≤ ∑ i, s i := Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ i)
    linarith
  have hGcoord' : ∀ s : Fin k → ℝ,
      (∃ i, Bg < s i) → (∑ j : Fin J, c j * ∏ l, Gt j l (s l)) = 0 := by
    intro s hs
    rw [← hGtf_eq]
    exact hGcoord s hs
  have happrox' : ∀ s : Fin k → ℝ, |(∑ j : Fin J, c j * ∏ l, Gt j l (s l)) - F s| ≤ el := by
    intro s
    rw [← hGtf_eq]
    exact happrox s
  intro i₀
  refine le_trans ?_ hbound
  refine margTensor_near_JFunc Gt (fun j i => (hGtsm j i).continuous) hGtcs
    (fun j i => ((hGtsm j i).continuous).integrable_of_hasCompactSupport (hGtcs j i))
    c i₀ cc hFc hCF0 hCF hBg0 hRB hel hFcoord hGcoord' happrox' hF0


/-! ## The marginal bound for the `J₂`-part

The `J₂`-loss bound `margLoss_le` needs a uniform bound `|tenP G c i T t| ≤ Bm` for the partial
marginal sum over the complement of the `J₁`-set.  It follows from the *marginal* uniform bound
`Σ_j |c_j| ∏_{l ≠ i} |G j l (t_l)| ≤ Bm'` of the thin localisation together with the thin
support of the `i`-th component (`|∫_{x>0} G j i| ≤ 6η·B`). -/

/-- The partial marginal tensor sum is bounded by `6η·B·Bm` on the orthant, given the marginal
uniform bound `Bm` and the halfline-integral bound `6η·B` for the `i`-th components. -/
theorem abs_tenP_le {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ) (c : Fin J → ℝ) (i₀ : Fin k)
    (S : Finset (Fin J)) {η B Bm : ℝ}
    (hint : ∀ j : Fin J, |∫ x in Set.Ioi (0:ℝ), G j i₀ x| ≤ 6 * η * B)
    (hBmarg : ∀ t : ({l : Fin k // l ≠ i₀} → ℝ),
      ∑ j : Fin J, |c j| * ∏ l : {l : Fin k // l ≠ i₀}, |G j (l : Fin k) (t l)| ≤ Bm)
    (hη : 0 ≤ η) (hB : 0 ≤ B) (hBm0 : 0 ≤ Bm) :
    ∀ t : ({l : Fin k // l ≠ i₀} → ℝ), (∀ l, 0 ≤ t l) →
      |tenP G c i₀ S t| ≤ 6 * η * B * Bm := by
  classical
  intro t ht
  have hterm : ∀ j : Fin J, |c j * (∫ x in Set.Ioi (0:ℝ), G j i₀ x) *
      ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l)| ≤
      (6 * η * B) * (|c j| * ∏ l : {l : Fin k // l ≠ i₀}, |G j (l : Fin k) (t l)|) := by
    intro j
    rw [abs_mul, abs_mul, Finset.abs_prod]
    have h6 : (0:ℝ) ≤ 6 * η * B := by positivity
    calc |c j| * |∫ x in Set.Ioi (0:ℝ), G j i₀ x| * ∏ l : {l : Fin k // l ≠ i₀}, |G j (l : Fin k) (t l)|
        ≤ |c j| * (6 * η * B) * ∏ l : {l : Fin k // l ≠ i₀}, |G j (l : Fin k) (t l)| := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hint j) (abs_nonneg _))
            (Finset.prod_nonneg fun l _ => abs_nonneg _)
      _ = (6 * η * B) * (|c j| * ∏ l : {l : Fin k // l ≠ i₀}, |G j (l : Fin k) (t l)|) := by ring
  rw [tenP]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc (∑ j ∈ S, |c j * (∫ x in Set.Ioi (0:ℝ), G j i₀ x) *
        ∏ l : {l : Fin k // l ≠ i₀}, G j (l : Fin k) (t l)|)
      ≤ ∑ j ∈ S, (6 * η * B) *
          (|c j| * ∏ l : {l : Fin k // l ≠ i₀}, |G j (l : Fin k) (t l)|) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ ≤ ∑ j : Fin J, (6 * η * B) *
          (|c j| * ∏ l : {l : Fin k // l ≠ i₀}, |G j (l : Fin k) (t l)|) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun j _ _ => mul_nonneg (by positivity)
            (mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun l _ => abs_nonneg _)))
    _ = (6 * η * B) * ∑ j : Fin J,
          (|c j| * ∏ l : {l : Fin k // l ≠ i₀}, |G j (l : Fin k) (t l)|) :=
        (Finset.mul_sum Finset.univ _ (6 * η * B)).symm
    _ ≤ (6 * η * B) * Bm := mul_le_mul_of_nonneg_left (hBmarg t) (by positivity)
    _ = 6 * η * B * Bm := by ring


/-- **The marginal bound with the thin structure.**  Version of `abs_tenP_le` where the
halfline-integral bound `6η·B` is derived from the thinness of the `i₀`-th components and their
uniform bound `B`. -/
theorem abs_tenP_le_thin {J k : ℕ} (G : Fin J → Fin k → ℝ → ℝ) (c : Fin J → ℝ) (i₀ : Fin k)
    (S : Finset (Fin J)) (β : Fin J → Fin k → ℝ) {η B Bm : ℝ}
    (hη : 0 ≤ η)
    (hthin : ∀ j l u, 0 ≤ u → G j l u ≠ 0 → β j l - 6 * η < u ∧ u < β j l)
    (hBbd : ∀ j l u, |G j l u| ≤ B)
    (hBmarg : ∀ t : ({l : Fin k // l ≠ i₀} → ℝ),
      ∑ j : Fin J, |c j| * ∏ l : {l : Fin k // l ≠ i₀}, |G j (l : Fin k) (t l)| ≤ Bm)
    (hB : 0 ≤ B) (hBm0 : 0 ≤ Bm) :
    ∀ t : ({l : Fin k // l ≠ i₀} → ℝ), (∀ l, 0 ≤ t l) →
      |tenP G c i₀ S t| ≤ 6 * η * B * Bm :=
  abs_tenP_le G c i₀ S (fun j => Commons.Analysis.Integral.abs_integral_Ioi_le_thin hη
    (fun u hu hne => hthin j i₀ u hu hne) (fun u => hBbd j i₀ u)) hBmarg hη hB hBm0

end Commons.NumberTheory.MaynardSieve
