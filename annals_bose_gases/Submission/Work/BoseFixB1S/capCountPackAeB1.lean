import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Submission.Work.BoseFixB1S.capCountPackB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-!
# `capCountPackAeB1`: the packing bound from an a.e. nonvanishing hypothesis

`Work.BoseFixB1S.capCountPackB1` proves the capacity/packing bound

`Σᵢ ∫_{abox} Φ² · 1_{supp χ_B}(xᵢ) ≤ 64 ((ℓd)³/r³) ∫_{abox} Φ²`

under the *pointwise* hypothesis that the potential `v` does not vanish on the whole ball of
radius `r` (`Metric.ball 0 r ⊆ Function.support v`).

Here we prove the same statement under the much weaker hypothesis that `v` vanishes only on a
*null* set of that ball.  The formalisation `capCountPackAeB1` is therefore **strictly stronger**
than the proved `capCountPackB1`, so it cannot be derived from it; the missing ingredient is the
measure-theoretic fact that the preimage of a Lebesgue-null set under the surjective linear map
`x ↦ x i - x j` is null (Fubini along the kernel).  We obtain it from
`MeasureTheory.ae_comp_linearMap_mem_iff` (the disintegration of Haar measure under a surjective
linear map) applied to the difference map `coordDiff i j`, with a measurable hull
`toMeasurable volume Z` of the null zero set of `v`.

The rest of the argument — the a.e. void structure `pairVoidAeB1`, the packing lemma
`Work.BoseBogFS.card_le_of_separated`, and the a.e. → integral step — is the same as in
`capCountPackB1`; the private helpers `norm_sub_le_sqrt_three_half` and `capPackCubeCardLe` of that
file are reproduced here (they are `private` there, hence not importable).
-/

/-- The difference of the `i`-th and `j`-th coordinates, as a linear map on configuration space. -/
def coordDiff {n : ℕ} (i j : Fin n) :
    (Submission.BoseGases.X n) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun x := x i - x j
  map_add' x y := by simp only [Pi.add_apply, sub_add_sub_comm]
  map_smul' c x := by simp only [Pi.smul_apply, smul_sub, RingHom.id_apply]

/-- `coordDiff i j` is surjective as soon as `i ≠ j`. -/
lemma coordDiff_surjective {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Function.Surjective (coordDiff i j) := by
  intro y
  refine ⟨Pi.single i y, ?_⟩
  simp [coordDiff, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)]

/-- **Preimage of a null set under the coordinate difference.**  If `v` vanishes only on a null
subset of the ball of radius `r`, then for a.e. configuration the pair difference `x i - x j`
avoids that null set; equivalently, `v (x i - x j) ≠ 0` whenever `dist (x i) (x j) < r`.

This is the only genuinely new ingredient of `capCountPackAeB1` compared with
`capCountPackB1`. -/
lemma ae_pair_v_ne_zero {n : ℕ} {ℓ r : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hZ0 : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        ({z | v z = 0} ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r) = 0)
    {i j : Fin n} (hij : i ≠ j) :
    ∀ᵐ x ∂(volume.restrict (Submission.BoseGases.abox n ℓ)),
      dist (x i) (x j) < r → v (x i - x j) ≠ 0 := by
  classical
  obtain ⟨Z, hZdef⟩ : ∃ Z : Set (EuclideanSpace ℝ (Fin 3)),
      Z = {z | v z = 0} ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r := ⟨_, rfl⟩
  have hZzero : (volume : Measure (EuclideanSpace ℝ (Fin 3))) Z = 0 := by
    rw [hZdef]; exact hZ0
  -- a measurable hull of the null set
  obtain ⟨Z', hZ'def⟩ : ∃ Z' : Set (EuclideanSpace ℝ (Fin 3)), Z' = toMeasurable volume Z :=
    ⟨_, rfl⟩
  have hZ'meas : MeasurableSet Z' := by rw [hZ'def]; exact measurableSet_toMeasurable _ _
  have hZ'zero : (volume : Measure (EuclideanSpace ℝ (Fin 3))) Z' = 0 := by
    rw [hZ'def, measure_toMeasurable]; exact hZzero
  have hZ'sub : Z ⊆ Z' := by rw [hZ'def]; exact subset_toMeasurable _ _
  -- the hull is avoided a.e. in the target space
  have hν : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))), y ∉ Z' := by
    rw [MeasureTheory.ae_iff]
    simpa using hZ'zero
  -- disintegration of Haar measure along the surjective difference map
  have hμ : ∀ᵐ x ∂(volume : Measure (Submission.BoseGases.X n)),
      coordDiff i j x ∉ Z' :=
    (MeasureTheory.ae_comp_linearMap_mem_iff (coordDiff i j) volume volume
      (coordDiff_surjective hij) (s := Z'ᶜ) hZ'meas.compl).2 hν
  have hvol' : (volume : Measure (Submission.BoseGases.X n))
      {x | coordDiff i j x ∈ Z'} = 0 := by
    rw [MeasureTheory.ae_iff] at hμ
    convert hμ using 2
    ext x; simp
  have hvol : (volume : Measure (Submission.BoseGases.X n))
      {x | coordDiff i j x ∈ Z} = 0 :=
    measure_mono_null (fun x hx => hZ'sub hx) hvol'
  -- the bad configurations in the box are contained in that preimage
  have hsub : {x : Submission.BoseGases.X n |
        ¬ (dist (x i) (x j) < r → v (x i - x j) ≠ 0)}
      ⊆ {x | coordDiff i j x ∈ Z} := by
    intro x hx
    have hlt : dist (x i) (x j) < r := by
      by_contra hcon
      exact hx (fun h => (hcon h).elim)
    have hv0 : v (x i - x j) = 0 := by
      by_contra hcon
      exact hx (fun _ => hcon)
    have h1 : v (coordDiff i j x) = 0 := by
      rw [show coordDiff i j x = x i - x j from rfl]; exact hv0
    have h2 : coordDiff i j x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r := by
      rw [Metric.mem_ball, dist_zero_right, show coordDiff i j x = x i - x j from rfl]
      simpa [dist_eq_norm] using hlt
    rw [hZdef]
    exact ⟨h1, h2⟩
  rw [MeasureTheory.ae_iff]
  refine le_antisymm ?_ bot_le
  calc (volume.restrict (Submission.BoseGases.abox n ℓ))
        {x : Submission.BoseGases.X n |
          ¬ (dist (x i) (x j) < r → v (x i - x j) ≠ 0)}
      ≤ (volume.restrict (Submission.BoseGases.abox n ℓ)) {x | coordDiff i j x ∈ Z} :=
        measure_mono hsub
    _ ≤ (volume : Measure (Submission.BoseGases.X n)) {x | coordDiff i j x ∈ Z} :=
        Measure.restrict_le_self _
    _ = 0 := hvol

/-- **The a.e. separation statement with the a.e. nonvanishing hypothesis.**  This is
`pairSepAeB1` with `Metric.ball 0 r ⊆ Function.support v` replaced by the a.e. form. -/
theorem pairSepAeAeB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R)
    (hball : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r)),
      v z ≠ 0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRℓ : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hden : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi
        (ℓ⁻¹ • z))
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hpair : Work.BoseFixB1.pairSum v M ℓ d u Φ = 0) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      Φ x ≠ 0 → ∀ i j : Fin n, i ≠ j →
        Submission.BoseGases.chiSmallB M ℓ d u (x i) ≠ 0 →
        Submission.BoseGases.chiSmallB M ℓ d u (x j) ≠ 0 → r ≤ dist (x i) (x j) := by
  classical
  -- the zero set of `v` inside the ball of radius `r` is null
  have hZ : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      ({z | v z = 0} ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r) = 0 := by
    rw [← Measure.restrict_apply' (s := Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r)
      (t := {z | v z = 0}) Metric.isOpen_ball.measurableSet]
    simpa using (MeasureTheory.ae_iff.mp hball)
  -- the void structure of the pairing word
  have hvoid := pairVoidAeB1 (v := v) h hv hv1 hR hv_supp hM hℓ hd hRℓ hRχ hden hΦc hpair
  -- a.e., pair differences at distance `< r` avoid the zero set of `v`
  have hsep : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      ∀ p : Fin n × Fin n, p.1 ≠ p.2 → dist (x p.1) (x p.2) < r →
        v (x p.1 - x p.2) ≠ 0 := by
    rw [Filter.eventually_all]
    intro p
    by_cases hp : p.1 = p.2
    · exact Filter.Eventually.of_forall (fun x hne => (hne hp).elim)
    · exact (ae_pair_v_ne_zero (v := v) (ℓ := ℓ) hZ (i := p.1) (j := p.2) hp).mono
        (fun x hx _ => hx)
  filter_upwards [hvoid, hsep] with x hx1 hx2
  intro hΦne i j hij hxi hxj
  by_contra hcon
  have hlt : dist (x i) (x j) < r := not_le.mp hcon
  have hvij : v (x i - x j) ≠ 0 := hx2 (i, j) hij hlt
  have h0 := hx1 hΦne i j hij
  rcases mul_eq_zero.mp h0 with h | h
  · exact hvij ((mul_eq_zero.mp h).resolve_left hxi)
  · exact hxj h

/-! ### The packing lemma (private in `capCountPackB1`, reproduced here) -/

/-- A point of `ℝ³` whose coordinate differences from `c` are all bounded by `L / 2` (i.e. lying
in the axis-parallel cube of side `L` centred at `c`) lies within `√3 · L / 2` of `c`. -/
private lemma norm_sub_le_sqrt_three_half_aeb {y c : EuclideanSpace ℝ (Fin 3)} {L : ℝ}
    (h : ∀ j : Fin 3, |(y - c).ofLp j| ≤ L / 2) :
    ‖y - c‖ ≤ Real.sqrt 3 * (L / 2) := by
  have hL2 : (0 : ℝ) ≤ L / 2 := le_trans (abs_nonneg _) (h 0)
  have h2 : ‖y - c‖ ^ 2 ≤ (Real.sqrt 3 * (L / 2)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ j : Fin 3, ‖(y - c).ofLp j‖ ^ 2
        ≤ ∑ _j : Fin 3, (L / 2) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hj := h j
          have hsq : ((y - c).ofLp j) ^ 2 ≤ (L / 2) ^ 2 := by
            rw [sq_le_sq, abs_of_nonneg hL2]
            exact hj
          rwa [Real.norm_eq_abs, sq_abs]
      _ = 3 * (L / 2) ^ 2 := by simp
      _ = (Real.sqrt 3 * (L / 2)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have := (sq_le_sq.mp h2)
  rwa [abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 3) hL2)] at this

/-- **Packing bound for the cutoff cube**: a finite family of points of the axis-parallel cube of
side `L` centred at `c`, pairwise at distance `≥ r`, with `r ≤ L / 16`, has at most `64 L³/r³`
members. -/
private theorem capPackCubeCardLe_aeb {ι : Type*} (S : Finset ι)
    (y : ι → EuclideanSpace ℝ (Fin 3)) {c : EuclideanSpace ℝ (Fin 3)} {L r : ℝ}
    (_hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L / 16)
    (hcube : ∀ i ∈ S, ∀ j : Fin 3, |(y i - c).ofLp j| ≤ L / 2)
    (hsep : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' → r ≤ dist (y i) (y i')) :
    (S.card : ℝ) ≤ 64 * (L ^ 3 / r ^ 3) := by
  have hR0 : (0 : ℝ) ≤ Real.sqrt 3 * (L / 2) :=
    mul_nonneg (Real.sqrt_nonneg 3) (by linarith)
  have hsep' : ∀ i j : {i // i ∈ S}, i ≠ j →
      r ≤ ‖(y i.1 - c) - (y j.1 - c)‖ := by
    intro i j hij
    have h := hsep i.1 i.2 j.1 j.2 (by simpa using hij)
    rw [dist_eq_norm] at h
    rwa [sub_sub_sub_cancel_right]
  have hnorm : ∀ i : {i // i ∈ S}, ‖y i.1 - c‖ ≤ Real.sqrt 3 * (L / 2) :=
    fun i => norm_sub_le_sqrt_three_half_aeb (hcube i.1 i.2)
  have hle := Work.BoseBogFS.card_le_of_separated (fun i : {i // i ∈ S} => y i.1 - c)
    (δ := r) (r := Real.sqrt 3 * (L / 2)) hr hR0 hsep' hnorm
  rw [Finset.card_univ, Fintype.card_coe] at hle
  have hbase : Real.sqrt 3 * (2 * (Real.sqrt 3 * (L / 2)) / r) + 2 = 3 * (L / r) + 2 := by
    have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    have hmain : Real.sqrt 3 * (2 * (Real.sqrt 3 * (L / 2)) / r) = 3 * (L / r) := by
      calc Real.sqrt 3 * (2 * (Real.sqrt 3 * (L / 2)) / r)
          = (Real.sqrt 3 * Real.sqrt 3) * (2 * (L / 2)) / r := by ring
        _ = 3 * (2 * (L / 2)) / r := by rw [h3]
        _ = 3 * (L / r) := by ring
    rw [hmain]
  rw [hbase] at hle
  have hLr : (16 : ℝ) ≤ L / r := by
    rw [le_div_iff₀ hr]
    linarith
  have hlin : 3 * (L / r) + 2 ≤ 4 * (L / r) := by linarith
  have hnonneg : (0 : ℝ) ≤ 3 * (L / r) + 2 := by linarith
  refine le_trans hle (le_trans (pow_le_pow_left₀ hnonneg hlin 3) ?_)
  rw [mul_pow, div_pow]
  norm_num

/-- The pointwise (a.e.) count bound: at an a.e. configuration with `Φ ≠ 0` the cutoff support
carries at most `64 (ℓd)³/r³` particles.  Same proof as `capCountPackB1.capCount_ae_le`, but with
the a.e. separation statement `pairSepAeAeB1`. -/
private theorem capCount_ae_le_aeb {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R)
    (hball : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r)),
      v z ≠ 0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRℓ : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hden : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi
        (ℓ⁻¹ • z))
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hpair : Work.BoseFixB1.pairSum v M ℓ d u Φ = 0) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ)),
      (∑ i : Fin n, (Φ x) ^ 2 *
          (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
            (fun _ => (1 : ℝ)) (x i))
        ≤ (64 * ((ℓ * d) ^ 3 / r ^ 3)) * (Φ x) ^ 2 := by
  classical
  have hsepae := pairSepAeAeB1 (v := v) h hv hv1 hR hr hrR hball hv_supp hM hℓ hd hRℓ hRχ hden
    hΦc hpair
  filter_upwards [hsepae] with x hx
  by_cases h0 : Φ x = 0
  · simp [h0]
  · have hcount : (∑ i : Fin n, (Function.support
            (Submission.BoseGases.chiSmallB M ℓ d u)).indicator (fun _ => (1 : ℝ)) (x i))
        ≤ 64 * ((ℓ * d) ^ 3 / r ^ 3) := by
      have h1 : (∑ i : Fin n, (Function.support
              (Submission.BoseGases.chiSmallB M ℓ d u)).indicator (fun _ => (1 : ℝ)) (x i))
          = ((Finset.univ.filter (fun i : Fin n =>
              x i ∈ Function.support (Submission.BoseGases.chiSmallB M ℓ d u))).card : ℝ) := by
        rw [← Finset.sum_boole
          (fun i : Fin n => x i ∈ Function.support (Submission.BoseGases.chiSmallB M ℓ d u))
          Finset.univ]
        exact Finset.sum_congr rfl (fun i _ => by rw [Set.indicator_apply])
      rw [h1]
      refine capPackCubeCardLe_aeb (S := Finset.univ.filter (fun i : Fin n =>
          x i ∈ Function.support (Submission.BoseGases.chiSmallB M ℓ d u))) (y := x)
        (c := (ℓ * d) • u) (L := ℓ * d) (r := r) (by positivity) hr (by linarith) ?_ ?_
      · intro i hi j
        have hne : Submission.BoseGases.chiSmallB M ℓ d u (x i) ≠ 0 :=
          Function.mem_support.mp (Finset.mem_filter.mp hi).2
        exact Submission.BoseGases.chiSmallB_support_small_box_dist hM hℓ hd hne j
      · intro i hi i' hi' hne'
        have h1' : Submission.BoseGases.chiSmallB M ℓ d u (x i) ≠ 0 :=
          Function.mem_support.mp (Finset.mem_filter.mp hi).2
        have h2' : Submission.BoseGases.chiSmallB M ℓ d u (x i') ≠ 0 :=
          Function.mem_support.mp (Finset.mem_filter.mp hi').2
        exact hx h0 i i' hne' h1' h2'
    calc (∑ i : Fin n, (Φ x) ^ 2 * (Function.support
            (Submission.BoseGases.chiSmallB M ℓ d u)).indicator (fun _ => (1 : ℝ)) (x i))
        = (Φ x) ^ 2 * (∑ i : Fin n, (Function.support
            (Submission.BoseGases.chiSmallB M ℓ d u)).indicator (fun _ => (1 : ℝ)) (x i)) := by
          rw [Finset.mul_sum]
      _ ≤ (Φ x) ^ 2 * (64 * ((ℓ * d) ^ 3 / r ^ 3)) :=
          mul_le_mul_of_nonneg_left hcount (sq_nonneg _)
      _ = (64 * ((ℓ * d) ^ 3 / r ^ 3)) * (Φ x) ^ 2 := by ring

theorem capCountPackAeB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) {R r : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hrR : r ≤ R)
    (hball : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) r)),
      v z ≠ 0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hRℓ : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (hden : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      1 / 2 ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi
        (ℓ⁻¹ • z))
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ}
    (hΦc : Continuous Φ)
    (hpair : Work.BoseFixB1.pairSum v M ℓ d u Φ = 0) :
    ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
          (fun _ => (1 : ℝ)) (x i)
      ≤ 64 * ((ℓ * d) ^ 3 / r ^ 3)
          * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  classical
  have hA : MeasurableSet (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)) :=
    measurableSet_support_chiSmallB hM u
  have hInti : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
        (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
          (fun _ => (1 : ℝ)) (x i))
      (Submission.BoseGases.abox n ℓ) :=
    fun i => integrableOn_sq_indicator_abox hℓ hA hΦc i
  have hInt2 : MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n => (Φ x) ^ 2) (Submission.BoseGases.abox n ℓ) :=
    integrableOn_sq_abox hℓ hΦc
  have hae := capCount_ae_le_aeb (v := v) h hv hv1 hR hr hrR hball hv_supp hM hℓ hd hRℓ hRχ hden
    hΦc hpair
  calc ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        (Φ x) ^ 2 * (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
          (fun _ => (1 : ℝ)) (x i)
      = ∫ x in Submission.BoseGases.abox n ℓ, ∑ i : Fin n,
          (Φ x) ^ 2 * (Function.support (Submission.BoseGases.chiSmallB M ℓ d u)).indicator
            (fun _ => (1 : ℝ)) (x i) :=
        (MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hInti i)).symm
    _ ≤ ∫ x in Submission.BoseGases.abox n ℓ,
          (64 * ((ℓ * d) ^ 3 / r ^ 3)) * (Φ x) ^ 2 :=
        MeasureTheory.integral_mono_ae
          (MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hInti i))
          (hInt2.const_mul _) hae
    _ = 64 * ((ℓ * d) ^ 3 / r ^ 3)
          * ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
        rw [MeasureTheory.integral_const_mul]

end

end Work.BoseFixB1S
