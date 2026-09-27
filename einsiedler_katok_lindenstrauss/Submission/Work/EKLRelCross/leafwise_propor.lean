import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.propor_aux
import Submission.Work.EKLRelCross.covariant_shape
import Submission.Work.EKLRelCross.measurableSet_nu_compact_lt
import Submission.Work.EKLRelCross.flower_family_exists
import Submission.Work.EKLRelCross.exists_shrink_nhds
import Submission.Work.EKLRelCross.ae_covariant_shape_all
import Submission.Work.EKLRelCross.ae_recurs_levels

/-!
# `Work.EKLRelCross.leafwise_propor` — (U5) of the frozen EKL contract (EKL (8))

**Statement.**  For a probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a horospherical subgroup
`U`, a diagonal element `a = aDiag t0` preserving `μ` and contracting `U`, and any leafwise
system `ν` for `(μ, U)`: for `μ`-a.e. `x`, if the right `u`-translate of `ν x` is proportional
to `ν x`, then it is equal to `ν x`.

## The proof (the `D_M` argument of EKL p. 13)

The hypothesis list contains no `A`-covariance of `ν`: that covariance is *not* a field of
`IsLeafwise` and has to be reconstructed, at the points and for the plaques that the argument
needs, from the `condexp` field (Pisa 7.17).

* **Geometric input (Pisa Cor. 6.15, "flowers").**  `flower_family_exists` supplies countably
  many plaque algebras `(Z i, m i)` with measurable bases `G i ⊆ Z i`, `μ (Z i) ≠ 0`,
  `μ (⋃ G i)ᶜ = 0` and
  `V 9 ∩ U ⊆ shape (m i) U x` for `x ∈ G i`.
* **`A`-covariance on the shapes (Pisa 7.17).**  `ae_covariant_shape_all` (built on
  `covariant_shape`, the single-plaque covariance, itself derived from the `condexp` field)
  gives, a.e. `x` and for every `(n, i)`, the proportionality
  `ν (aDiag (n • t0) • x) C = c * (ν x).map (conj by aDiag (n • t0)) C` for all Borel
  `C ⊆ shape (m i) U (aDiag (n • t0) • x)`, whenever `aDiag (n • t0) • x` is a free point of
  `X' ∩ Z i`.
* **Recurrence at a single level (Poincaré + the countable level family).**
  `ae_recurs_levels` (built on `ae_exists_level_frequently` of `propor_aux`) gives, a.e. `x`,
  one pair `(i, M)` such that the orbit of `x` under `T = aDiag t0 • ·` meets
  `X' ∩ G i ∩ {ν· (Ucl U 9) < M}` infinitely often.
* **The mass computation.**  Fix `k` and a recurrence time `n` beyond the threshold where
  `γ⁻¹ := aDiag (n • t0) · (u⁻¹)^k · (aDiag (n • t0))⁻¹ ∈ V 1` (here `hcontr` is used).  Both
  `Box1 U` and `Box1 U · γ⁻¹` lie in `V 9 ∩ U`, hence in the shape at `T^n x`, and so
  `mass_translate` (with the iterated quasi-invariance `map_conj_mul_pow`) computes
  `ν (T^n x) (Box1 U · γ⁻¹) = c^k`; since `Box1 U · γ⁻¹ ⊆ Ucl U 9` and
  `ν (T^n x) (Ucl U 9) < M`, this gives `c^k < M` for every `k`, whence `c ≤ 1` by
  `le_one_of_pow_lt`.
* Running the same argument with `u⁻¹` and `c⁻¹` gives `c⁻¹ ≤ 1`, i.e. `1 ≤ c`.  Finally `c = 0`
  contradicts `ν x (Box1 U) = 1` (through `(ν x).map (· * u) (U) = ν x U`) and `c = ⊤` is
  excluded by `c ≤ 1`; so `c = 1` and `(ν x).map (· * u) = ν x`.

The helper lemmas of the argument live in `Submission.Work.EKLRelCross.propor_aux`; the two
a.e. packaging steps are `ae_covariant_shape_all` and `ae_recurs_levels`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLRelCross


/-! ## The target -/

theorem leafwise_propor (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    ∀ᵐ x ∂μ, ∀ u ∈ U, ∀ c : ENNReal,
        (ν x).map (fun g => g * u) = c • ν x → (ν x).map (fun g => g * u) = ν x := by
  classical
  -- ## The geometric input: flowers at radius `9` (Pisa Cor. 6.15)
  obtain ⟨ι, hcount, Z, mm, G, hZ, hGmeas, hGsub, hZpos, hshape, hGcover⟩ :=
    flower_family_exists h2 μ U hU t0 ht0 hcontr 9 (by norm_num)
  haveI : Countable ι := hcount
  -- ## The compact set of the `D_M` argument and its level sets
  have hKc : IsCompact (Ucl U 9) := isCompact_Ucl hU.1 9
  -- ## The contracting diagonal self-map
  set T : X3 → X3 := fun y => aDiag t0 • y with hTdef
  have hT : ∀ n : ℕ, ∀ y : X3, T^[n] y = aDiag (n • t0) • y := by
    intro n y
    rw [hTdef, smul_iterate, aDiag_nsmul]
  -- ## The `A`-covariance at every iterate of `t0` and every flower
  have hcovall := ae_covariant_shape_all (μ := μ) hU hL t0 ht0 hZ hZpos
  -- ## The a.e. recurrence on a single level of a single flower
  have hrecall := ae_recurs_levels (μ := μ) hL ht0 hGmeas hGcover hKc
  -- ## The orbits stay in `X'` and at `U`-free points
  have hfreeae : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 := ae_free_orbit h2 μ U hU t0 ht0 hcontr
  set F : Set X3 := {y | ∀ u ∈ U, u • y = y → u = 1} with hFdef
  have hFnull : μ Fᶜ = 0 := by
    have h := MeasureTheory.ae_iff.mp hfreeae
    simpa [hFdef, Set.compl_def] using h
  have hYae : ∀ᵐ x ∂μ, x ∈ X' ∩ F := by
    rw [MeasureTheory.ae_iff]
    have hset : {a : X3 | ¬ a ∈ X' ∩ F} = X'ᶜ ∪ Fᶜ := by
      rw [← Set.compl_inter]
      rfl
    rw [hset]
    exact measure_union_null hL.conull hFnull
  have horbit : ∀ᵐ x ∂μ, ∀ n : ℕ, T^[n] x ∈ X' ∧ T^[n] x ∈ F := by
    rw [MeasureTheory.ae_all_iff]
    intro n
    exact (ht0.iterate n).quasiMeasurePreserving.ae hYae
  filter_upwards [hcovall, hrecall, horbit] with x hcovx hrecx hxorb
  have hxX : x ∈ X' := by
    have h := (hxorb 0).1
    rwa [Function.iterate_zero_apply] at h
  intro u hu c hqi
  obtain ⟨i, M, hrecM⟩ := hrecx
  -- ## The normalisation of the leafwise measures along the orbit
  have hnorm : ∀ n : ℕ, ν (T^[n] x) (Box1 U) = 1 := fun n => hL.normalised _ (hxorb n).1
  -- ## The key bound: `c ^ k < M` for every `k`
  have key : ∀ (w : SL3), w ∈ U → ∀ (c : ENNReal), (ν x).map (fun g => g * w) = c • ν x →
      ∀ k : ℕ, c ^ k < (M : ENNReal) := by
    intro w hw c hcw k
    -- the threshold beyond which the `k`-th conjugate of `w` is small
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (eventual_conj_pow_mem_V (U := U) (t0 := t0) (ε := 1) one_pos hcontr w⁻¹ (U.inv_mem hw) k)
    -- a recurrence time beyond that threshold
    obtain ⟨n, hnN, hyX, hyG, hyM⟩ := hrecM N
    have hyZ : T^[n] x ∈ Z i := hGsub i hyG
    obtain ⟨cn, hcn0, hcnt, hcnC⟩ :=
      hcovx (n, i) hxX (by simpa [hT n x] using hyX) (by simpa [hT n x] using hyZ)
        (by simpa [hFdef, hT n x] using (hxorb n).2)
    -- the geometry: `Box1 U` and `Box1 U · γ⁻¹` lie in the shape at the recurrence point
    have hγV : (aDiag (n • t0) * w ^ k * (aDiag (n • t0))⁻¹)⁻¹ ∈ V 1 := by
      have hgrp : (aDiag (n • t0) * w ^ k * (aDiag (n • t0))⁻¹)⁻¹
          = aDiag t0 ^ n * (w⁻¹) ^ k * (aDiag t0 ^ n)⁻¹ := by
        rw [aDiag_nsmul]
        group
      rw [hgrp]
      exact hN n hnN
    have hγVs : (aDiag (n • t0) * w ^ k * (aDiag (n • t0))⁻¹)⁻¹ ∈ V (((9 : ℝ) - 1) / 8) := by
      rw [show ((9 : ℝ) - 1) / 8 = 1 by norm_num]
      exact hγV
    have hγU : (aDiag (n • t0) * w ^ k * (aDiag (n • t0))⁻¹)⁻¹ ∈ U :=
      U.inv_mem (hU.2.1 (n • t0) (w ^ k) (pow_mem hw k))
    have hbox₁ : Box1 U ⊆ shape (mm i) U (aDiag (n • t0) • x) := by
      intro g hg
      exact hshape i _ (by simpa [hT n x] using hyG)
        ⟨Box1_subset_V (by norm_num : (1 : ℝ) < 9) hg, hg.1⟩
    have hbox₂ : (fun g : SL3 => g * (aDiag (n • t0) * w ^ k * (aDiag (n • t0))⁻¹)⁻¹)
        '' Box1 U ⊆ shape (mm i) U (aDiag (n • t0) • x) := by
      rintro g ⟨b, hb, rfl⟩
      refine hshape i _ (by simpa [hT n x] using hyG) ⟨?_, ?_⟩
      · exact Box1_mul_subset_V (R := 9) (by norm_num)
          (hγVs) b hb
      · exact U.mul_mem hb.1 hγU
    have hγmeas : MeasurableSet ((fun g : SL3 =>
        g * (aDiag (n • t0) * w ^ k * (aDiag (n • t0))⁻¹)⁻¹) '' (Box1 U)) := by
      have hpre : (fun g : SL3 => g * (aDiag (n • t0) * w ^ k * (aDiag (n • t0))⁻¹)) ⁻¹'
            (Box1 U)
          = (fun g : SL3 => g * (aDiag (n • t0) * w ^ k * (aDiag (n • t0))⁻¹)⁻¹)
              '' (Box1 U) := by
        ext g
        simp only [Set.mem_preimage, Set.mem_image]
        constructor
        · intro hg
          exact ⟨g * (aDiag (n • t0) * w ^ k * (aDiag (n • t0))⁻¹), hg, by group⟩
        · rintro ⟨b, hb, rfl⟩
          show b * (aDiag (n • t0) * w ^ k * (aDiag (n • t0))⁻¹)⁻¹
            * (aDiag (n • t0) * w ^ k * (aDiag (n • t0))⁻¹) ∈ Box1 U
          rw [mul_assoc, inv_mul_cancel, mul_one]
          exact hb
      rw [← hpre]
      exact (measurableSet_Box1 hU.1).preimage (by fun_prop)
    have hmass := mass_translate (ν := ν) (U := U) (x := x) (y := T^[n] x)
        (a := aDiag (n • t0)) (u := w) (k := k) (c := c) (c' := cn)
        (S := shape (mm i) U (aDiag (n • t0) • x))
        (measurableSet_Box1 hU.1) hγmeas
        (by
          intro C hC hCS
          simpa [hT n x] using hcnC C hC hCS)
        hbox₁ hbox₂
        (map_conj_mul_pow (a := aDiag (n • t0)) (u := w) (c := c) hcw k)
        (hnorm n)
    -- the mass of the translate is `c ^ k` and sits inside the compact set
    have hsub : (fun g : SL3 => g * (aDiag (n • t0) * w ^ k * (aDiag (n • t0))⁻¹)⁻¹)
        '' Box1 U ⊆ Ucl U 9 := by
      rintro g ⟨b, hb, rfl⟩
      exact ⟨U.mul_mem hb.1 hγU, fun p q => le_of_lt
        (Box1_mul_subset_V (R := 9) (by norm_num) (hγVs) b hb p q)⟩
    calc c ^ k = ν (T^[n] x) ((fun g : SL3 =>
              g * (aDiag (n • t0) * w ^ k * (aDiag (n • t0))⁻¹)⁻¹) '' Box1 U) := hmass.symm
      _ ≤ ν (T^[n] x) (Ucl U 9) := measure_mono hsub
      _ < (M : ENNReal) := hyM
  -- ## `c ≤ 1`
  have hcle : c ≤ 1 := le_one_of_pow_lt (key u hu c hqi)
  -- ## `c ≠ 0`
  have hc0 : c ≠ 0 := by
    intro h0
    have hUmeas : MeasurableSet (U : Set SL3) := hU.1.measurableSet
    have hpre : (fun g : SL3 => g * u) ⁻¹' (U : Set SL3) = (U : Set SL3) := by
      ext g
      simp only [Set.mem_preimage]
      constructor
      · intro hg
        have h2' : (g * u) * u⁻¹ ∈ U := U.mul_mem hg (U.inv_mem hu)
        simpa using h2'
      · intro hg
        exact U.mul_mem hg hu
    have h1 : (ν x).map (fun g : SL3 => g * u) (U : Set SL3) = ν x (U : Set SL3) := by
      rw [Measure.map_apply (by fun_prop) hUmeas, hpre]
    have hzero : (ν x).map (fun g : SL3 => g * u) (U : Set SL3) = 0 := by
      rw [hqi, h0]
      simp
    have h2' : ν x (U : Set SL3) = 0 := by rw [← h1, hzero]
    have h3 : (1 : ENNReal) ≤ ν x (U : Set SL3) := by
      rw [← hL.normalised x hxX]
      exact measure_mono fun g hg => hg.1
    rw [h2'] at h3
    exact absurd h3 (not_le.mpr zero_lt_one)
  -- ## `c ≠ ⊤`
  have hctop : c ≠ ⊤ := fun h => absurd (h ▸ hcle) (not_le.mpr ENNReal.one_lt_top)
  -- ## the same bound for `u⁻¹`, giving `1 ≤ c`
  have hinv : (ν x).map (fun g => g * u⁻¹) = c⁻¹ • ν x := map_mul_inv_quasi hc0 hctop hqi
  have hge : (1 : ENNReal) ≤ c := by
    have h2' : c⁻¹ ≤ 1 := le_one_of_pow_lt (key u⁻¹ (U.inv_mem hu) c⁻¹ hinv)
    exact (ENNReal.inv_le_one).mp h2'
  rw [hqi, le_antisymm hcle hge, one_smul]

end Work.EKLRelCross
