import Mathlib
import Submission.Work.Surf.defs
import Submission.Work.Surf.zeros_finite_euc
import Submission.Work.Surf.exists_uniform_separating_radius
import Submission.Work.Surf.exists_unique_zero_near

/-!
# Persistence of the number of zeros in the square under a small `C¹` perturbation

The engine of `Work.Surf.smooth_reduction`: the number of zeros in the unit square of a `C¹` map which
vanishes nowhere on the boundary and whose zeros in the square are regular is stable under `C¹`-small
perturbations, and the perturbed map again has only finitely many zeros there.

The two ingredients extracted from the proof are proved in sibling files:

* `Work.Surf.zeros_finite_euc` — the zeros of `F` in the square are finite and isolated;
* `Work.Surf.exists_uniform_separating_radius` — finitely many disjoint balls, one around each zero;
* `Work.Surf.exists_unique_zero_near` — Banach's fixed point theorem for `x ↦ x - (fderiv ℝ F p)⁻¹ (G x)`
  gives exactly one zero of `G` in the ball around each zero of `F`.
-/

set_option linter.style.haveILetI false

namespace Work.Surf

open Set Metric
open scoped Topology

noncomputable section

local notation "Eucl2" => EuclideanSpace ℝ (Fin 2)

/-- **Persistence of the number of zeros in the square under a small `C¹` perturbation.**  Let
`F : 𝔼² → 𝔼²` be `C¹` and nonzero on the boundary of the unit square, with every zero in the square a
regular point (surjective derivative).  Then there is `δ > 0` such that every `C¹` map
`G : 𝔼² → 𝔼²` with `‖G x - F x‖ < δ` **and** `‖fderiv ℝ G x - fderiv ℝ F x‖ < δ` for all `x` in the
square has *finitely many* zeros in the square, exactly as many as `F`:

`({x ∈ sqBox | G x = 0}).Finite ∧ ({x ∈ sqBox | G x = 0}).ncard = ({x ∈ sqBox | F x = 0}).ncard`.

This is the "zeros" half of `Work.Surf.smooth_reduction`; the `C¹`-closeness (not merely `C⁰`) is
essential — a merely small uniform perturbation of `F = id` can create arbitrarily many zeros.

Proof.  The zeros of `F` in the square are finitely many and lie in the *interior* of the square
(`hbdry`); each is isolated, with invertible derivative (`hreg`).  Choose disjoint small closed balls
`Bᵢ ⊆ sqBox`, one around each zero `pᵢ` of `F`, and let `m > 0` be the minimum of `‖F‖` on the compact
remainder `sqBox \ ⋃ Bᵢ`; take `δ < m/2`.  For `G` with `‖G - F‖ < δ` on the square:

* `G` has no zero outside `⋃ Bᵢ`, since there `‖G‖ ≥ ‖F‖ - δ > 0`;
* writing `Lᵢ = fderiv ℝ F pᵢ` (invertible) the map `Φ x = x - Lᵢ⁻¹ (G x)` satisfies
  `fderiv ℝ Φ x = Lᵢ⁻¹ (Lᵢ - fderiv ℝ G x)`, whose operator norm is `< 1` for `δ` small enough
  (since `Lᵢ - fderiv ℝ G x = (fderiv ℝ F pᵢ - fderiv ℝ F x) + (fderiv ℝ F x - fderiv ℝ G x)` and
  `fderiv ℝ F` is continuous, so the first summand is small on a small ball), and `Φ` maps a small
  ball around `pᵢ` into itself (because `G pᵢ = 0 + small` and `Lᵢ` is invertible).  Hence `Φ` is a
  contraction with exactly one fixed point in that ball (Banach fixed point theorem), i.e. `G` has
  exactly one zero there.  This gives a bijection between the zero sets, hence the equality of
  cardinalities, and the finiteness. -/
theorem ncard_zeros_persist
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ 1 F)
    (hbdry : ∀ x ∈ Work.Surf.sqBdry, F x ≠ 0)
    (hreg : ∀ x ∈ Work.Surf.sqBox, F x = 0 → Function.Surjective (fderiv ℝ F x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
      ContDiff ℝ 1 G → (∀ x ∈ Work.Surf.sqBox, ‖G x - F x‖ < δ) →
      (∀ x ∈ Work.Surf.sqBox, ‖fderiv ℝ G x - fderiv ℝ F x‖ < δ) →
      ({x ∈ Work.Surf.sqBox | G x = 0} : Set (EuclideanSpace ℝ (Fin 2))).Finite ∧
        ({x ∈ Work.Surf.sqBox | G x = 0} : Set (EuclideanSpace ℝ (Fin 2))).ncard =
          ({x ∈ Work.Surf.sqBox | F x = 0} : Set (EuclideanSpace ℝ (Fin 2))).ncard := by
  classical
  have hmem_int : ∀ x : Eucl2, x ∈ sqBox → x ∉ sqBdry → x ∈ interior sqBox := by
    intro x hx h
    have hne0 : x 0 ≠ 0 := fun h0 => h ⟨hx, Or.inl h0⟩
    have hne1 : x 0 ≠ 1 := fun h1 => h ⟨hx, Or.inr (Or.inl h1)⟩
    have hne2 : x 1 ≠ 0 := fun h0 => h ⟨hx, Or.inr (Or.inr (Or.inl h0))⟩
    have hne3 : x 1 ≠ 1 := fun h1 => h ⟨hx, Or.inr (Or.inr (Or.inr h1))⟩
    have h0mem : x 0 ∈ Ioo (0:ℝ) 1 :=
      ⟨lt_of_le_of_ne hx.1.1 (Ne.symm hne0), lt_of_le_of_ne hx.1.2 hne1⟩
    have h1mem : x 1 ∈ Ioo (0:ℝ) 1 :=
      ⟨lt_of_le_of_ne hx.2.1 (Ne.symm hne2), lt_of_le_of_ne hx.2.2 hne3⟩
    set T : Set Eucl2 := {y | y 0 ∈ Ioo (0:ℝ) 1 ∧ y 1 ∈ Ioo (0:ℝ) 1} with hT
    have hTopen : IsOpen T := by
      have hc0 : Continuous fun y : Eucl2 => y 0 :=
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0).continuous
      have hc1 : Continuous fun y : Eucl2 => y 1 :=
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1).continuous
      have hTeq : T = (fun y : Eucl2 => y 0) ⁻¹' Ioo (0:ℝ) 1 ∩
          (fun y : Eucl2 => y 1) ⁻¹' Ioo (0:ℝ) 1 := by
        ext y; simp [T]
      rw [hTeq]
      exact (isOpen_Ioo.preimage hc0).inter (isOpen_Ioo.preimage hc1)
    have hTsub : T ⊆ sqBox := by
      rintro y ⟨hy0, hy1⟩
      exact ⟨⟨hy0.1.le, hy0.2.le⟩, ⟨hy1.1.le, hy1.2.le⟩⟩
    exact interior_maximal hTsub hTopen ⟨h0mem, h1mem⟩
  have hfinmin : ∀ (ι : Type) (hι : Finite ι) (c : ι → ℝ), (∀ i, 0 < c i) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ c i := by
    intro ι hι c hc
    haveI := hι
    rcases isEmpty_or_nonempty ι with hι' | hι'
    · exact ⟨1, one_pos, fun i => (hι'.false i).elim⟩
    · haveI : Fintype ι := Fintype.ofFinite ι
      refine ⟨Finset.univ.inf' Finset.univ_nonempty c, ?_, fun i => ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro i _
        exact hc i
      · exact Finset.inf'_le c (Finset.mem_univ i)
  set Z : Set Eucl2 := {x ∈ sqBox | F x = 0} with hZdef
  have hZfin : Z.Finite := zeros_finite_euc F hF hbdry hreg
  haveI : Finite Z := hZfin.to_subtype
  let Ee : (p : Z) → Eucl2 ≃L[ℝ] Eucl2 := fun p =>
    ContinuousLinearEquiv.ofBijective (fderiv ℝ F (p : Eucl2))
      (by
        rw [LinearMap.ker_eq_bot]
        exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).mpr
          (hreg (p : Eucl2) p.2.1 p.2.2))
      (LinearMap.range_eq_top.mpr (hreg (p : Eucl2) p.2.1 p.2.2))
  let Ei : Z → (Eucl2 →L[ℝ] Eucl2) := fun p => ((Ee p).symm : Eucl2 →L[ℝ] Eucl2)
  have hZint : ∀ x ∈ Z, x ∈ interior sqBox := fun x hx =>
    hmem_int x hx.1 (fun hb => hbdry x hb hx.2)
  have hexists_R : ∀ p : Z, ∃ R : ℝ, 0 < R ∧ closedBall (p : Eucl2) R ⊆ sqBox ∧
      ∀ x ∈ closedBall (p : Eucl2) R,
        ‖fderiv ℝ F x - fderiv ℝ F p‖ ≤ 1 / (4 * (‖Ei p‖ + 1)) := by
    intro p
    obtain ⟨ε₁, hε₁pos, hε₁sub⟩ := Metric.mem_nhds_iff.mp
      (mem_interior_iff_mem_nhds.mp (hZint p p.2))
    have hηpos : 0 < 1 / (4 * (‖Ei p‖ + 1)) := by
      have h1 : (0:ℝ) ≤ ‖Ei p‖ := norm_nonneg _
      exact one_div_pos.mpr (by linarith)
    have hgcont : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
    obtain ⟨ε₂, hε₂pos, hε₂⟩ := (Metric.continuous_iff.mp hgcont) (p : Eucl2)
      (1 / (4 * (‖Ei p‖ + 1))) hηpos
    refine ⟨min (ε₁ / 2) (ε₂ / 2), lt_min (by linarith) (by linarith), ?_, ?_⟩
    · exact (Metric.closedBall_subset_ball
        (lt_of_le_of_lt (min_le_left _ _) (by linarith))).trans hε₁sub
    · intro x hx
      rw [mem_closedBall] at hx
      have hx2 : dist x (p : Eucl2) < ε₂ := by
        have := min_le_right (ε₁ / 2) (ε₂ / 2)
        linarith
      have h := hε₂ x hx2
      simpa [dist_eq_norm] using le_of_lt h
  choose R hRpos hRsub hRclose using hexists_R
  let S : Eucl2 → Set Eucl2 := fun p => if hp : p ∈ Z then ball p (R ⟨p, hp⟩) else univ
  have hSopen : ∀ p ∈ Z, IsOpen (S p) := by
    intro p hp
    simp only [S, dif_pos hp]
    exact isOpen_ball
  have hSself : ∀ p ∈ Z, p ∈ S p := by
    intro p hp
    simp only [S, dif_pos hp]
    exact Metric.mem_ball_self (hRpos ⟨p, hp⟩)
  obtain ⟨r, hrpos, hrsub, hrdisj⟩ := exists_uniform_separating_radius hZfin S hSopen hSself
  have hrsub' : ∀ p : Z, closedBall (p : Eucl2) r ⊆ ball (p : Eucl2) (R p) := by
    intro p
    have h := hrsub (p : Eucl2) p.2
    simpa only [S, dif_pos p.2] using h
  have hrdisj' : ∀ p q : Z, p ≠ q →
      Disjoint (closedBall (p : Eucl2) r) (closedBall (q : Eucl2) r) := by
    intro p q hpq
    exact hrdisj (p : Eucl2) p.2 (q : Eucl2) q.2 (fun h => hpq (Subtype.ext h))
  let c : Z → ℝ := fun p => min (1 / (4 * (‖Ei p‖ + 1))) (r / (2 * (‖Ei p‖ + 1)))
  have hcpos : ∀ p : Z, 0 < c p := by
    intro p
    refine lt_min ?_ ?_
    · have h1 : (0:ℝ) ≤ ‖Ei p‖ := norm_nonneg _
      exact one_div_pos.mpr (by linarith)
    · have h1 : (0:ℝ) ≤ ‖Ei p‖ := norm_nonneg _
      exact div_pos hrpos (by linarith)
  obtain ⟨ε, hεpos, hεle⟩ := hfinmin ↥Z hZfin.to_subtype c hcpos
  let U : Set Eucl2 := ⋃ p : Z, ball (p : Eucl2) (r / 2)
  have hUopen : IsOpen U := isOpen_iUnion fun p => isOpen_ball
  have hKcpt : IsCompact (sqBox \ U) :=
    isCompact_sqBox_euc.of_isClosed_subset (isClosed_sqBox_euc.sdiff hUopen) (Set.sdiff_subset)
  have hFne : ∀ x ∈ sqBox \ U, F x ≠ 0 := by
    rintro x ⟨hxbox, hxU⟩ hx0
    exact hxU (mem_iUnion.mpr ⟨⟨x, hxbox, hx0⟩, Metric.mem_ball_self (by linarith)⟩)
  obtain ⟨m, hmpos, hmle⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ sqBox \ U, m ≤ ‖F x‖ := by
    rcases (sqBox \ U).eq_empty_or_nonempty with hE | hne
    · exact ⟨1, one_pos, by simp [hE]⟩
    · obtain ⟨x, hx, hxmin⟩ := hKcpt.exists_isMinOn (f := fun x : Eucl2 => ‖F x‖) hne
        hF.continuous.norm.continuousOn
      exact ⟨‖F x‖, norm_pos_iff.mpr (hFne x hx), fun y hy => hxmin hy⟩
  refine ⟨min ε m / 2, ?_, ?_⟩
  · have hmin : 0 < min ε m := lt_min hεpos hmpos
    linarith
  intro G hG hG0 hG1
  have hδε : min ε m / 2 ≤ ε := by
    have h1 : min ε m ≤ ε := min_le_left _ _
    have h2 : 0 < min ε m := lt_min hεpos hmpos
    linarith
  have hδm : min ε m / 2 < m := by
    have h1 : min ε m ≤ m := min_le_right _ _
    have h2 : 0 < min ε m := lt_min hεpos hmpos
    linarith
  have hlocal : ∀ p : Z, ∃! x : Eucl2, x ∈ closedBall (p : Eucl2) r ∧ G x = 0 := by
    intro p
    have hL : (Ee p : Eucl2 →L[ℝ] Eucl2) = fderiv ℝ F (p : Eucl2) := by
      simp only [Ee]
      exact ContinuousLinearEquiv.coe_ofBijective _ _ _
    refine exists_unique_zero_near F G hG p.2.2 (Ee p) hL (ρ := r) (δ := min ε m / 2) hrpos
      ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hxR : x ∈ closedBall (p : Eucl2) (R p) := Metric.ball_subset_closedBall (hrsub' p hx)
      exact hRclose p x hxR
    · have h1 : min ε m / 2 ≤ ε := hδε
      have h2 : ε ≤ c p := hεle p
      have h3 : c p ≤ 1 / (4 * (‖Ei p‖ + 1)) := min_le_left _ _
      exact le_trans h1 (le_trans h2 h3)
    · have h1 : min ε m / 2 ≤ ε := hδε
      have h2 : ε ≤ c p := hεle p
      have h3 : c p ≤ r / (2 * (‖Ei p‖ + 1)) := min_le_right _ _
      exact le_trans h1 (le_trans h2 h3)
    · exact hG0 (p : Eucl2) p.2.1
    · intro x hx
      have hxR : x ∈ closedBall (p : Eucl2) (R p) := Metric.ball_subset_closedBall (hrsub' p hx)
      exact hG1 x (hRsub p hxR)
  let xstar : Z → Eucl2 := fun p => Classical.choose (hlocal p)
  have hxs_mem : ∀ p : Z, xstar p ∈ closedBall (p : Eucl2) r :=
    fun p => (Classical.choose_spec (hlocal p)).1.1
  have hxs_zero : ∀ p : Z, G (xstar p) = 0 :=
    fun p => (Classical.choose_spec (hlocal p)).1.2
  have hxs_uniq : ∀ p : Z, ∀ y : Eucl2, y ∈ closedBall (p : Eucl2) r → G y = 0 →
      y = xstar p :=
    fun p y hy hy0 => (Classical.choose_spec (hlocal p)).2 y ⟨hy, hy0⟩
  have hxs_sqBox : ∀ p : Z, xstar p ∈ sqBox :=
    fun p => hRsub p (Metric.ball_subset_closedBall (hrsub' p (hxs_mem p)))
  have hzeros_subset : ∀ x ∈ sqBox, G x = 0 → x ∈ U := by
    intro x hxbox hx0
    by_contra hxU
    have h1 : m ≤ ‖F x‖ := hmle x ⟨hxbox, hxU⟩
    have h2 : ‖G x - F x‖ < m := lt_of_lt_of_le (hG0 x hxbox) (le_of_lt hδm)
    have h3 : 0 < ‖G x‖ := by
      have htri : ‖F x‖ ≤ ‖F x - G x‖ + ‖G x‖ := by
        simpa using norm_add_le (F x - G x) (G x)
      rw [norm_sub_rev] at htri
      linarith
    rw [hx0, norm_zero] at h3
    exact lt_irrefl 0 h3
  have hxs_ball : ∀ p : Z, xstar p ∈ ball (p : Eucl2) (r / 2) := by
    intro p
    have hU : xstar p ∈ U := hzeros_subset (xstar p) (hxs_sqBox p) (hxs_zero p)
    obtain ⟨q, hq⟩ := mem_iUnion.mp hU
    have hq' : xstar p ∈ closedBall (q : Eucl2) r :=
      Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hq)
    have hpq : p = q := by
      by_contra hne
      exact (Set.disjoint_left.mp (hrdisj' p q hne)) (hxs_mem p) hq'
    rw [hpq] at hq ⊢
    exact hq
  have hsurj : ∀ b ∈ ({x ∈ sqBox | G x = 0} : Set Eucl2), ∃ p : Z, xstar p = b := by
    intro b hb
    obtain ⟨hbx, hbz⟩ := hb
    obtain ⟨p, hp⟩ := mem_iUnion.mp (hzeros_subset b hbx hbz)
    have hp' : b ∈ closedBall (p : Eucl2) r :=
      Metric.closedBall_subset_closedBall (by linarith) (Metric.ball_subset_closedBall hp)
    exact ⟨p, (hxs_uniq p b hp' hbz).symm⟩
  have hinj : ∀ p q : Z, xstar p = xstar q → p = q := by
    intro p q hpq
    by_contra hne
    have h1 : xstar p ∈ closedBall (p : Eucl2) r := hxs_mem p
    have h2 : xstar p ∈ closedBall (q : Eucl2) r := by
      rw [hpq]
      exact Metric.closedBall_subset_closedBall (by linarith)
        (Metric.ball_subset_closedBall (hxs_ball q))
    exact (Set.disjoint_left.mp (hrdisj' p q hne)) h1 h2
  have hGfin : ({x ∈ sqBox | G x = 0} : Set Eucl2).Finite := by
    have hsub : ({x ∈ sqBox | G x = 0} : Set Eucl2) ⊆ xstar '' (Set.univ : Set Z) := by
      rintro b hb
      obtain ⟨p, hp⟩ := hsurj b hb
      exact ⟨p, mem_univ p, hp⟩
    exact (Set.finite_univ.image xstar).subset hsub
  have hncard : ({x ∈ sqBox | G x = 0} : Set Eucl2).ncard = Z.ncard :=
    (Set.ncard_congr (s := Z) (t := ({x ∈ sqBox | G x = 0} : Set Eucl2))
      (fun a ha => xstar ⟨a, ha⟩)
      (fun a ha => ⟨hxs_sqBox ⟨a, ha⟩, hxs_zero ⟨a, ha⟩⟩)
      (fun a b ha hb hab => Subtype.ext_iff.mp (hinj ⟨a, ha⟩ ⟨b, hb⟩ hab))
      (fun b hb => by
        obtain ⟨p, hp⟩ := hsurj b hb
        exact ⟨p.1, p.2, hp⟩)).symm
  exact ⟨hGfin, by simpa only [hZdef] using hncard⟩

end

end Work.Surf
