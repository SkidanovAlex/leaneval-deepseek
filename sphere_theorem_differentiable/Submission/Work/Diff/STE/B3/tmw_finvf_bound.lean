import Mathlib
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.tmNom_aux
import Submission.Work.Diff.STE.B3.transport_Mf_second

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

set_option maxHeartbeats 1000000

/-!
# Bounds on the inverse frame matrix `Finvf` and on its first jet `tmDFin`

The transport identity of layer B3 is stated on the closed `(2 σ j + δ)`-ball of flat coordinates,
where the chart matrix `Gf` of a section has to be inverted.  The analytic input for the ensuing
periodisation/energy estimates is that the *inverse frame matrix* `Finvf` (the entries of
`(Ff)⁻¹`), together with its first jet `tmDFin`, is bounded by a constant which is **uniform** in
the chart index `j` and in the point `z` of that ball.

This module proves `Work.Diff.STE.B3.tmw_finvf_bound`: from the (open, hence local) hypothesis that
on the ball the flat coordinate lies in the chart target and that `det (Ff) ≠ 0` there, one obtains
such a uniform constant `C`.

Route:

* `Ff z` is `C^∞` at every point of the ball (`Ff_contDiffAt`, using target membership);
* the ball is compact (the model space is finite dimensional) and non-empty, so the entries of `Ff`
  are bounded by a constant `Cf` and `|det (Ff ·)|` has a positive minimum `c` on it;
* Cramer's rule (`Matrix.inv_def`, `Matrix.adjugate_apply`, `Matrix.det_apply'`) then bounds every
  entry of `(Ff z)⁻¹` by `Cf` and `c` — this is `tmw_matrix_inv_entry_bound` below;
* the first jet is bounded by compactness of the continuous map
  `z ↦ fderiv (fun y => (Ff y)⁻¹ i a) z (single c 1)`, whose continuity follows from the `C^∞`
  regularity of the inverse entries at each point of the ball (`tmNom_inv_entry_ContDiffAt`) and
  `ContDiffAt.continuousAt_fderiv` — this is `tmw_fderiv_inv_entry_bound` below.
-/

/-- **The determinant of a matrix with bounded entries.**  If every entry of `B` is bounded by `M`
in absolute value, then `|det B| ≤ n! · M ^ n` (the sign of a permutation is a unit of `ℤ`). -/
private lemma tmw_det_abs_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)
    (hM : ∀ i j, |B i j| ≤ M) :
    |B.det| ≤ (n.factorial : ℝ) * M ^ n := by
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      |(↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, B (σ i) i| ≤ M ^ n := by
    intro σ
    rw [abs_mul, abs_unit_intCast (Equiv.Perm.sign σ), one_mul, Finset.abs_prod]
    calc ∏ i : Fin n, |B (σ i) i| ≤ ∏ _i : Fin n, M :=
          Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hM (σ i) i)
      _ = M ^ n := Fin.prod_const n M
  have h1 : |∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, B (σ i) i|
      ≤ ∑ σ : Equiv.Perm (Fin n), |(↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, B (σ i) i| :=
    Finset.abs_sum_le_sum_abs _ Finset.univ
  have h2 : (∑ σ : Equiv.Perm (Fin n), |(↑↑(Equiv.Perm.sign σ) : ℝ) * ∏ i, B (σ i) i|)
      ≤ ∑ _σ : Equiv.Perm (Fin n), M ^ n := Finset.sum_le_sum (fun σ _ => hterm σ)
  have h3 : (∑ _σ : Equiv.Perm (Fin n), M ^ n) = (n.factorial : ℝ) * M ^ n := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  rw [Matrix.det_apply']
  exact le_trans h1 (le_trans h2 (le_of_eq h3))

/-- **The entries of the inverse of a matrix with bounded entries and determinant bounded away from
zero are bounded.**  Cramer's rule: `A⁻¹ = (det A)⁻¹ • A.adjugate`; every entry of the adjugate is a
determinant of a matrix whose entries are bounded by `1` in the replaced row and by `M` elsewhere,
hence by `n! · (max M 1) ^ n`. -/
private lemma tmw_matrix_inv_entry_bound {n : ℕ} (M c : ℝ) (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : Fin n → Fin n → ℝ,
      (∀ i j, |A i j| ≤ M) → c ≤ |(Matrix.of A).det| →
        ∀ i j, |(Matrix.of A)⁻¹ i j| ≤ C := by
  refine ⟨c⁻¹ * ((n.factorial : ℝ) * (max M 1) ^ n),
    mul_nonneg (le_of_lt (inv_pos.mpr hc))
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_trans zero_le_one (le_max_right M 1)) n)), ?_⟩
  intro A hA hdet i j
  have hdet0 : (Matrix.of A).det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hdet
    exact absurd hdet (not_le.mpr hc)
  have hadj : |(Matrix.of A).adjugate i j| ≤ (n.factorial : ℝ) * (max M 1) ^ n := by
    rw [Matrix.adjugate_apply]
    refine tmw_det_abs_le _ (max M 1) ?_
    intro p q
    rw [Matrix.updateRow_apply]
    by_cases hp : p = j
    · rw [if_pos hp]
      refine le_trans ?_ (le_max_right M 1)
      by_cases hq : q = i
      · subst hq
        simp
      · rw [Pi.single_eq_of_ne hq]
        simp
    · rw [if_neg hp]
      simpa only [Matrix.of_apply] using le_trans (hA p q) (le_max_left M 1)
  have hinv : |(Matrix.of A).det|⁻¹ ≤ c⁻¹ :=
    (inv_le_inv₀ (abs_pos.mpr hdet0) hc).mpr hdet
  have hkey : (Matrix.of A)⁻¹ i j = ((Matrix.of A).det)⁻¹ * (Matrix.of A).adjugate i j := by
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
    rw [congrFun Ring.inverse_eq_inv' ((Matrix.of A).det)]
  rw [hkey, abs_mul, abs_inv]
  exact mul_le_mul hinv hadj (abs_nonneg _) (le_of_lt (inv_pos.mpr hc))

/-- **The first partial derivatives of the inverse-matrix entries are bounded on a compact set.**
If the entries of a matrix family `f` are `C^∞` at every point of a compact set `K` and
`det (f z) ≠ 0` on `K`, then the coordinate derivatives of the entries of the inverse are bounded
on `K` by a constant. -/
private lemma tmw_fderiv_inv_entry_bound {n : ℕ} {f : (Fin n → ℝ) → (Fin n → Fin n → ℝ)}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hsm : ∀ z ∈ K, ∀ p q, ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (fun y => f y p q) z)
    (hdet : ∀ z ∈ K, (Matrix.of (f z)).det ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ c i j : Fin n,
      |fderiv ℝ (fun y => ((Matrix.of (f y))⁻¹) i j) z (Pi.single c 1)| ≤ C := by
  have hcont : ∀ (c i j : Fin n), ContinuousOn
      (fun z : Fin n → ℝ => fderiv ℝ (fun y => ((Matrix.of (f y))⁻¹) i j) z (Pi.single c 1)) K := by
    intro c i j z hz
    have hcd : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun y => ((Matrix.of (f y))⁻¹) i j) z :=
      tmNom_inv_entry_ContDiffAt (X := fun y => Matrix.of (f y))
        (fun p q => by simpa only [Matrix.of_apply] using hsm z hz p q) (hdet z hz) i j
    exact ((hcd.continuousAt_fderiv (by simp)).clm_apply continuousAt_const).continuousWithinAt
  have hb : ∀ p : Fin n × (Fin n × Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K,
      |fderiv ℝ (fun y => ((Matrix.of (f y))⁻¹) p.2.1 p.2.2) z (Pi.single p.1 1)| ≤ C := by
    intro p
    obtain ⟨c, i, j⟩ := p
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hcont c i j)
    exact ⟨max C 0, le_max_right C 0, fun z hz =>
      le_trans (by simpa only [Real.norm_eq_abs] using hC z hz) (le_max_left C 0)⟩
  choose Cb hCb0 hCb using hb
  refine ⟨∑ p : Fin n × (Fin n × Fin n), Cb p,
    Finset.sum_nonneg (fun p _ => hCb0 p), ?_⟩
  intro z hz c i j
  exact le_trans (hCb (c, i, j) z hz)
    (Finset.single_le_sum (fun p _ => hCb0 p) (Finset.mem_univ (c, i, j)))

theorem tmw_finvf_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) {δ : ℝ} (hδ : 0 < δ)
    (hreg : ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
        (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z)).det ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
        ∀ i a : Fin (Module.finrank ℝ E),
        |Work.Diff.STE.B3.Finvf (I := I) (M := M) D j z i a| ≤ C) ∧
      (∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
        ∀ c i a : Fin (Module.finrank ℝ E),
        |Work.Diff.STE.B3.tmDFin (I := I) (M := M) D j z c i a| ≤ C) := by
  classical
  -- the uniform bound on each single chart
  have key : ∀ j : ι₀, ∃ Cj : ℝ, 0 ≤ Cj ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ →
        ∀ i a : Fin (Module.finrank ℝ E), |Finvf (I := I) (M := M) D j z i a| ≤ Cj) ∧
      (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ →
        ∀ c i a : Fin (Module.finrank ℝ E), |tmDFin (I := I) (M := M) D j z c i a| ≤ Cj) := by
    intro j
    -- the closed flat ball, on which everything is uniform
    set K : Set (Fin (Module.finrank ℝ E) → ℝ) :=
      Metric.closedBall 0 (2 * D.σ j + δ) with hKdef
    have hrpos : 0 < 2 * D.σ j + δ := by
      have := D.hσ j
      linarith
    have hmem : ∀ z : Fin (Module.finrank ℝ E) → ℝ, z ∈ K ↔ ‖z‖ ≤ 2 * D.σ j + δ := by
      intro z
      rw [hKdef, Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hKc : IsCompact K := by
      rw [hKdef]
      exact isCompact_closedBall 0 (2 * D.σ j + δ)
    have hKne : K.Nonempty :=
      ⟨0, by rw [hKdef]; exact Metric.mem_closedBall_self hrpos.le⟩
    have hregK : ∀ z ∈ K,
        Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
          (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0 :=
      fun z hz => hreg j z ((hmem z).mp hz)
    have hsmFf : ∀ z ∈ K, ∀ p q : Fin (Module.finrank ℝ E),
        ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (fun y => Ff (I := I) (M := M) D j y p q) z :=
      fun z hz p q => Ff_contDiffAt (I := I) (M := M) D j p q (hregK z hz).1
    -- (1) the entries of `Ff` are bounded on `K`
    have hFfentry : ∀ pq : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        ∃ c : ℝ, 0 ≤ c ∧ ∀ z ∈ K, |Ff (I := I) (M := M) D j z pq.1 pq.2| ≤ c := by
      intro pq
      obtain ⟨p, q⟩ := pq
      have hcont : ContinuousOn
          (fun z : Fin (Module.finrank ℝ E) → ℝ => Ff (I := I) (M := M) D j z p q) K := by
        intro z hz
        exact ((hsmFf z hz p q).continuousAt).continuousWithinAt
      obtain ⟨c, hc⟩ := hKc.exists_bound_of_continuousOn hcont
      refine ⟨max c 0, le_max_right c 0, fun z hz => ?_⟩
      exact le_trans (by simpa only [Real.norm_eq_abs] using hc z hz) (le_max_left c 0)
    choose Cfe hCfe0 hCfe using hFfentry
    have hCF0 : 0 ≤ ∑ pq : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Cfe pq :=
      Finset.sum_nonneg (fun pq _ => hCfe0 pq)
    have hCfb : ∀ z ∈ K, ∀ p q : Fin (Module.finrank ℝ E),
        |Ff (I := I) (M := M) D j z p q| ≤
          ∑ pq : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Cfe pq := by
      intro z hz p q
      exact le_trans (hCfe (p, q) z hz)
        (Finset.single_le_sum (fun pq _ => hCfe0 pq) (Finset.mem_univ (p, q)))
    -- (2) `|det (Ff ·)|` has a positive minimum on `K`
    have hdetcont : ContinuousOn
        (fun z : Fin (Module.finrank ℝ E) → ℝ => |(Matrix.of (Ff (I := I) (M := M) D j z)).det|)
        K := by
      intro z hz
      have hcd : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
          (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            (Matrix.of (Ff (I := I) (M := M) D j y)).det) z :=
        tmNom_det_ContDiffAt (X := fun y => Matrix.of (Ff (I := I) (M := M) D j y))
          (fun p q => by
            have h := hsmFf z hz p q
            simpa only [Matrix.of_apply] using h)
      exact (hcd.continuousAt.abs).continuousWithinAt
    obtain ⟨z₀, hz₀K, hmin⟩ := hKc.exists_isMinOn hKne hdetcont
    have hcdpos : 0 < |(Matrix.of (Ff (I := I) (M := M) D j z₀)).det| :=
      abs_pos.mpr (hregK z₀ hz₀K).2
    have hcd : ∀ z ∈ K, |(Matrix.of (Ff (I := I) (M := M) D j z₀)).det| ≤
        |(Matrix.of (Ff (I := I) (M := M) D j z)).det| := isMinOn_iff.mp hmin
    -- (3) Cramer's rule bounds the entries of the inverse
    obtain ⟨CM, hCM0, hCM⟩ := tmw_matrix_inv_entry_bound (n := Module.finrank ℝ E)
      (∑ pq : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), Cfe pq)
      |(Matrix.of (Ff (I := I) (M := M) D j z₀)).det| hCF0 hcdpos
    -- (4) compactness bounds the first jet of the inverse
    obtain ⟨Cd, hCd0, hCd⟩ := tmw_fderiv_inv_entry_bound (n := Module.finrank ℝ E)
      (f := fun y => Ff (I := I) (M := M) D j y) hKc
      (fun z hz p q => hsmFf z hz p q) (fun z hz => (hregK z hz).2)
    refine ⟨max CM Cd, le_trans hCM0 (le_max_left CM Cd), ?_, ?_⟩
    · intro z hz i a
      have hzK : z ∈ K := (hmem z).mpr hz
      have h := hCM (Ff (I := I) (M := M) D j z) (fun p q => hCfb z hzK p q) (hcd z hzK) i a
      exact le_trans (by simpa only [Finvf] using h) (le_max_left CM Cd)
    · intro z hz c i a
      have hzK : z ∈ K := (hmem z).mpr hz
      have h := hCd z hzK c i a
      exact le_trans (by simpa only [tmDFin, Work.Diff.STE.pdR, Finvf] using h)
        (le_max_right CM Cd)
  choose Cj hprop using key
  refine ⟨∑ j, Cj j, Finset.sum_nonneg (fun j _ => (hprop j).1), ?_, ?_⟩
  · intro j z hz i a
    exact le_trans ((hprop j).2.1 z hz i a)
      (Finset.single_le_sum (fun j _ => (hprop j).1) (Finset.mem_univ j))
  · intro j z hz c i a
    exact le_trans ((hprop j).2.2 z hz c i a)
      (Finset.single_le_sum (fun j _ => (hprop j).1) (Finset.mem_univ j))

end Work.Diff.STE.B3
