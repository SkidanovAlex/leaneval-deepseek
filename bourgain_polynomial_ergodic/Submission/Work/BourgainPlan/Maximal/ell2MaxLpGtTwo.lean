import Mathlib
import Submission.Commons.Analysis.MeasureTheory.minkowski_lintegral_sum
import Submission.Work.BourgainPlan.Maximal.dyMaxStrongTypeENNReal
import Submission.Work.BourgainPlan.Maximal.lintegral_rpow_enorm_eq_layercake
import Submission.Work.BourgainPlan.Maximal.lintegral_mul_mul_le
import Submission.Work.BourgainPlan.Maximal.ell2Maximal
import Submission.Work.BourgainPlan.Maximal.dyMaxSharpCZ
import Submission.Work.BourgainPlan.Maximal.ell2MaxAux
import Submission.Work.BourgainPlan.Maximal.ell2MaxLp
import Submission.Work.BourgainPlan.Maximal.ell2MaxLpLtTwo
import Submission.Work.BourgainPlan.Maximal.ell2MaxWeakOne
import Submission.Work.BourgainPlan.Maximal.dyadicMaximal

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace Work.BourgainPlan.Maximal

/-! ### Elementary `ℝ≥0∞` arithmetic -/

/-- For `0 < t ≤ s`, `a^s = a^t * a^(s-t)`. -/
lemma rpow_eq_rpow_mul_rpow_sub {a : ℝ≥0∞} {s t : ℝ} (ht : 0 < t) (hts : t ≤ s) :
    a ^ s = a ^ t * a ^ (s - t) := by
  rcases lt_or_eq_of_le hts with hlt | rfl
  · rcases eq_or_ne a 0 with ha | ha
    · subst ha
      rw [ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < s),
        ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < s - t), mul_zero]
    rcases eq_or_ne a ⊤ with haT | haT
    · subst haT
      rw [ENNReal.top_rpow_of_pos (by linarith : (0:ℝ) < s),
        ENNReal.top_rpow_of_pos ht,
        ENNReal.top_rpow_of_pos (by linarith : (0:ℝ) < s - t), ENNReal.top_mul_top]
    · rw [mul_comm, ← ENNReal.rpow_add _ _ ha haT,
        add_comm, add_tsub_cancel_of_le hts]
  · rw [sub_self, ENNReal.rpow_zero, mul_one]

/-! ### `dyMax` and suprema -/

/-- `dyMax` commutes with the pointwise supremum of a monotone sequence of measurable
functions. -/
theorem dyMax_iSup {ψ : ℕ → ℝ → ℝ≥0∞} (hψ : ∀ N, Measurable (ψ N)) (hmono : Monotone ψ) :
    dyMax (fun y => ⨆ N, ψ N y) = fun x => ⨆ N, dyMax (ψ N) x := by
  funext x
  refine le_antisymm ?_ ?_
  · unfold dyMax
    refine iSup_le fun n => iSup_le fun k => iSup_le fun hx => ?_
    have h1 : ∫⁻ y in dyCell n k, (⨆ N, ψ N y) = ⨆ N, ∫⁻ y in dyCell n k, ψ N y :=
      lintegral_iSup (fun N => hψ N) hmono
    calc ENNReal.ofReal ((2:ℝ) ^ n)⁻¹ * ∫⁻ y in dyCell n k, (⨆ N, ψ N y)
        = ENNReal.ofReal ((2:ℝ) ^ n)⁻¹ * (⨆ N, ∫⁻ y in dyCell n k, ψ N y) := by rw [h1]
      _ = ⨆ N, ENNReal.ofReal ((2:ℝ) ^ n)⁻¹ * ∫⁻ y in dyCell n k, ψ N y :=
          ENNReal.mul_iSup _ _
      _ ≤ ⨆ N, dyMax (ψ N) x :=
          iSup_le fun N => le_iSup_of_le N
            (le_iSup_of_le n (le_iSup_of_le k (le_iSup_of_le hx le_rfl)))
  · exact iSup_le fun N => dyMax_mono (fun y => le_iSup (fun N => ψ N y) N) x

/-- For a finite family of monotone sequences of `ℝ≥0∞`, the supremum of the sums is the sum of
the suprema. -/
lemma iSup_finset_sum_eq {ι : Type*} [Fintype ι] {f : ι → ℕ → ℝ≥0∞}
    (h : ∀ i, Monotone (f i)) :
    (⨆ N, ∑ i, f i N) = ∑ i, ⨆ N, f i N := by
  have hsummono : Monotone fun N => ∑ i, f i N :=
    fun a b hab => Finset.sum_le_sum fun i _ => h i hab
  exact tendsto_nhds_unique (tendsto_atTop_iSup hsummono)
    (tendsto_finsetSum _ fun i _ => tendsto_atTop_iSup (h i))

/-- The `θ`-th power commutes with the supremum of a monotone sequence (`θ ≥ 0`). -/
lemma iSup_rpow_eq {b : ℕ → ℝ≥0∞} (hmono : Monotone b) {θ : ℝ} (hθ : 0 ≤ θ) :
    (⨆ N, b N) ^ θ = ⨆ N, (b N) ^ θ := by
  have hmono' : Monotone fun N => (b N) ^ θ :=
    fun a b hab => ENNReal.rpow_le_rpow (hmono hab) hθ
  have h1 : Tendsto (fun N => (b N) ^ θ) atTop (𝓝 ((⨆ N, b N) ^ θ)) :=
    ((ENNReal.continuous_rpow_const (y := θ)).tendsto (⨆ N, b N)).comp
      (tendsto_atTop_iSup hmono)
  have h2 : Tendsto (fun N => (b N) ^ θ) atTop (𝓝 (⨆ N, (b N) ^ θ)) :=
    tendsto_atTop_iSup hmono'
  exact tendsto_nhds_unique h1 h2



/-- For `y, z > 0`, `a^(y+z) = a^y * a^z` (no side conditions on `a`). -/
lemma rpow_add_eq_mul {a : ℝ≥0∞} {y z : ℝ} (hy : 0 < y) (hz : 0 < z) :
    a ^ (y + z) = a ^ y * a ^ z := by
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    rw [ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < y + z),
      ENNReal.zero_rpow_of_pos hy, ENNReal.zero_rpow_of_pos hz, zero_mul]
  rcases eq_or_ne a ⊤ with haT | haT
  · subst haT
    rw [ENNReal.top_rpow_of_pos hy, ENNReal.top_rpow_of_pos hz,
      ENNReal.top_rpow_of_pos (by linarith : (0:ℝ) < y + z)]
    exact ENNReal.top_mul_top.symm
  · exact ENNReal.rpow_add y z ha haT

/-- `a ^ (2:ℝ) = a * a`. -/
lemma rpow_two_eq_mul (a : ℝ≥0∞) : a ^ (2:ℝ) = a * a := by
  rw [show (2:ℝ) = 1 + 1 by norm_num, rpow_add_eq_mul (by norm_num) (by norm_num),
    ENNReal.rpow_one]

/-- The `p`-th moment of the `ℓ²`-valued dyadic maximal function is finite as soon as the
components' scalar dyadic maximal functions have finite `p`-th moment. -/
lemma lintegral_ell2Max_lt_top {n : ℕ} {p : ℝ} (hp : 2 < p) {f : Fin n → ℝ → ℝ}
    (hfin : ∀ t, ∫⁻ x, (dyMax (fun y => ‖f t y‖ₑ) x) ^ p < ⊤) :
    ∫⁻ x, (ell2Max f x) ^ (p / 2) < ⊤ := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hpq : p.HolderConjugate (p / (p - 1)) := by
    rw [Real.holderConjugate_iff]
    refine ⟨hp1, ?_⟩
    have hpne : (p:ℝ) ≠ 0 := by linarith
    have hp1ne : (p - 1 : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  have hpoint : ∀ x, (ell2Max f x) ^ (p / 2)
      ≤ (∑ t : Fin n, (dyMax (fun y => ‖f t y‖ₑ) x) ^ p) * (n : ℝ≥0∞) ^ (p - 1) := by
    intro x
    set a : Fin n → ℝ≥0∞ := fun t => dyMax (fun y => ‖f t y‖ₑ) x with hadef
    have hsq : ∑ t : Fin n, (a t) ^ (2:ℝ) ≤ (∑ t : Fin n, a t) ^ (2:ℝ) := by
      have hmul : (∑ t : Fin n, a t) * (∑ t : Fin n, a t) = ∑ t, ∑ s, a t * a s :=
        Finset.sum_mul_sum Finset.univ Finset.univ a a
      rw [rpow_two_eq_mul, hmul]
      refine Finset.sum_le_sum fun t _ => ?_
      rw [rpow_two_eq_mul]
      exact Finset.single_le_sum (f := fun s => a t * a s) (fun s _ => zero_le) (Finset.mem_univ t)
    have hstep : (∑ t : Fin n, (a t) ^ (2:ℝ)) ^ (p / 2) ≤ (∑ t : Fin n, a t) ^ p := by
      refine (ENNReal.rpow_le_rpow hsq (by positivity)).trans (le_of_eq ?_)
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    have hholder := Commons.Analysis.MeasureTheory.ennreal_finset_sum_mul_le_holder
      (t := Finset.univ) (x := a) (y := fun _ : Fin n => (1 : ℝ≥0∞)) hpq
    have hsum1 : (∑ t : Fin n, a t * 1) = ∑ t : Fin n, a t := by simp
    have hsum2 : (∑ t : Fin n, (1 : ℝ≥0∞) ^ (p / (p - 1))) = (n : ℝ≥0∞) := by simp
    rw [hsum1, hsum2] at hholder
    have hraised : (∑ t : Fin n, a t) ^ p
        ≤ (∑ t : Fin n, (a t) ^ p) * (n : ℝ≥0∞) ^ (p - 1) := by
      have h := ENNReal.rpow_le_rpow hholder hp0.le
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le] at h
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h
      have e1 : (1:ℝ) / p * p = 1 := by
        have hpne : (p:ℝ) ≠ 0 := by linarith
        field_simp
      have e2 : (1:ℝ) / (p / (p - 1)) * p = p - 1 := by
        have hpne : (p:ℝ) ≠ 0 := by linarith
        have hp1ne : (p - 1 : ℝ) ≠ 0 := by linarith
        field_simp
      rw [e1, e2, ENNReal.rpow_one] at h
      exact h
    calc (ell2Max f x) ^ (p / 2)
        = (∑ t : Fin n, (a t) ^ (2:ℝ)) ^ (p / 2) := by
          rw [ell2Max]
      _ ≤ (∑ t : Fin n, a t) ^ p := hstep
      _ ≤ (∑ t : Fin n, (a t) ^ p) * (n : ℝ≥0∞) ^ (p - 1) := hraised
  have hinner : Measurable fun x => ∑ t : Fin n, (dyMax (fun y => ‖f t y‖ₑ) x) ^ p :=
    Finset.measurable_sum _ fun t _ =>
      (ENNReal.continuous_rpow_const (y := p)).measurable.comp (dyMax_measurable _)
  calc ∫⁻ x, (ell2Max f x) ^ (p / 2)
      ≤ ∫⁻ x, (∑ t : Fin n, (dyMax (fun y => ‖f t y‖ₑ) x) ^ p) * (n : ℝ≥0∞) ^ (p - 1) :=
        lintegral_mono hpoint
    _ = (∑ t : Fin n, ∫⁻ x, (dyMax (fun y => ‖f t y‖ₑ) x) ^ p) * (n : ℝ≥0∞) ^ (p - 1) := by
        rw [lintegral_mul_const _ hinner, lintegral_finsetSum]
        intro t _
        exact (ENNReal.continuous_rpow_const (y := p)).measurable.comp (dyMax_measurable _)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.sum_lt_top.mpr fun t _ => hfin t)
        (ENNReal.rpow_lt_top_of_nonneg (by linarith : (0:ℝ) ≤ p - 1) (by simp))



/-! ### The weighted Calderón--Zygmund (Cotlar) inequality for the dyadic maximal function -/

/-- For `a : ℝ≥0∞` and a constant `c`,
`∫_{t>0} c·1_{ofReal t < a} dt = c·a`. -/
lemma lintegral_Ioi_if_lt (a c : ℝ≥0∞) :
    ∫⁻ t in Set.Ioi (0:ℝ), (if ENNReal.ofReal t < a then c else 0) = c * a := by
  rcases eq_top_or_lt_top a with rfl | ha
  · have hfun : (fun t : ℝ => if ENNReal.ofReal t < ⊤ then c else 0) = fun _ => c := by
      funext t; rw [if_pos ENNReal.ofReal_lt_top]
    rw [hfun, setLIntegral_const, Real.volume_Ioi]
  · have hset : {t : ℝ | t ∈ Set.Ioi (0:ℝ) ∧ ENNReal.ofReal t < a} = Set.Ioo 0 a.toReal := by
      ext t
      rw [Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_Ioi]
      constructor
      · rintro ⟨ht, hlt⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le ha.ne).mp hlt⟩
      · rintro ⟨ht, hlt⟩
        exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht.le ha.ne).mpr hlt⟩
    have hfun : (fun t : ℝ => (Set.Ioi (0:ℝ)).indicator
        (fun t => if ENNReal.ofReal t < a then c else 0) t)
        = (fun t : ℝ => {t : ℝ | t ∈ Set.Ioi (0:ℝ) ∧ ENNReal.ofReal t < a}.indicator
            (fun _ => c) t) := by
      funext t
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases h : ENNReal.ofReal t < a <;> simp [h, Set.mem_Ioi]
    rw [← lintegral_indicator measurableSet_Ioi (fun t => if ENNReal.ofReal t < a then c else 0),
      hfun, hset, lintegral_indicator measurableSet_Ioo (fun _ => c), setLIntegral_const,
      Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal ha.ne]

/-- **The weighted Calderón--Zygmund inequality for the dyadic maximal function**: at every level
`c`, `c·∫_{dyMax ψ > c} w ≤ ∫_{dyMax ψ > c} ψ·dyMax w`. -/
lemma czWeighted {ψ w : ℝ → ℝ≥0∞} {c : ℝ≥0∞} (hc : 0 < c) (hψ : ∫⁻ x, ψ x < ⊤) :
    c * ∫⁻ x in {x : ℝ | c < dyMax ψ x}, w x
      ≤ ∫⁻ x in {x : ℝ | c < dyMax ψ x}, ψ x * dyMax w x := by
  classical
  have hEeq : {x : ℝ | c < dyMax ψ x}
      = ⋃ p : {q : ℤ × ℤ // q ∈ czMax ψ c}, dyCell p.1.1 p.1.2 := by
    rw [levelSet_eq_iUnion_czMax (ψ := ψ) hc hψ]
    exact (Set.iUnion_subtype (p := fun q : ℤ × ℤ => q ∈ czMax ψ c)
      (s := fun q => dyCell q.1.1 q.1.2)).symm
  have hdisj : Pairwise (Function.onFun Disjoint
      fun p : {q : ℤ × ℤ // q ∈ czMax ψ c} => dyCell p.1.1 p.1.2) :=
    fun p q hpq => czMax_disjoint p.2 q.2 (fun h => hpq (Subtype.ext h))
  have hmeas : ∀ p : {q : ℤ × ℤ // q ∈ czMax ψ c}, MeasurableSet (dyCell p.1.1 p.1.2) :=
    fun p => dyCell_measurable _ _
  have hcell : ∀ p : {q : ℤ × ℤ // q ∈ czMax ψ c},
      c * ∫⁻ y in dyCell p.1.1 p.1.2, w y ≤ ∫⁻ y in dyCell p.1.1 p.1.2, ψ y * dyMax w y := by
    intro p
    obtain ⟨⟨n, k⟩, hp⟩ := p
    have hA0 : ENNReal.ofReal ((2:ℝ)^n) ≠ 0 := (ENNReal.ofReal_pos.mpr (zpow_two_pos n)).ne'
    have hAT : ENNReal.ofReal ((2:ℝ)^n) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmem : c < (ENNReal.ofReal ((2:ℝ)^n))⁻¹ * ∫⁻ y in dyCell n k, ψ y := by
      simpa only [czCells, Set.mem_ofPred_eq, ofReal_zpow_inv] using czMax_mem_czCells hp
    have hcvol : c * ENNReal.ofReal ((2:ℝ)^n) < ∫⁻ y in dyCell n k, ψ y :=
      mul_inv_mul_lt hA0 hAT hmem
    set D : ℝ≥0∞ := (ENNReal.ofReal ((2:ℝ)^n))⁻¹ * ∫⁻ y in dyCell n k, w y with hDdef
    have hDw : ∀ y ∈ dyCell n k, D ≤ dyMax w y := by
      intro y hy
      have hidx : dyIdx n y = k := dyIdx_eq_of_mem_cell hy
      have h1 : D = dyAvg w n y := by rw [hDdef, dyAvg, hidx, ofReal_zpow_inv]
      rw [h1]
      exact dyAvg_le_dyMax w n y
    have hcellw : ∫⁻ y in dyCell n k, w y = ENNReal.ofReal ((2:ℝ)^n) * D := by
      rw [hDdef, ← mul_assoc, ENNReal.mul_inv_cancel hA0 hAT, one_mul]
    calc c * ∫⁻ y in dyCell n k, w y
        = c * (ENNReal.ofReal ((2:ℝ)^n) * D) := by rw [hcellw]
      _ = c * ENNReal.ofReal ((2:ℝ)^n) * D := by rw [mul_assoc]
      _ ≤ (∫⁻ y in dyCell n k, ψ y) * D := mul_le_mul_left hcvol.le D
      _ ≤ ∫⁻ y in dyCell n k, ψ y * D := lintegral_mul_const_le D ψ
      _ ≤ ∫⁻ y in dyCell n k, ψ y * dyMax w y := by
          rw [← lintegral_indicator (dyCell_measurable n k) (fun y => ψ y * D),
            ← lintegral_indicator (dyCell_measurable n k) (fun y => ψ y * dyMax w y)]
          refine lintegral_mono fun y => ?_
          by_cases hy : y ∈ dyCell n k
          · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
            exact mul_le_mul_right (hDw y hy) _
          · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  calc c * ∫⁻ x in {x : ℝ | c < dyMax ψ x}, w x
      = c * ∑' p : {q : ℤ × ℤ // q ∈ czMax ψ c}, ∫⁻ y in dyCell p.1.1 p.1.2, w y := by
        rw [hEeq, lintegral_iUnion hmeas hdisj]
    _ = ∑' p : {q : ℤ × ℤ // q ∈ czMax ψ c}, c * ∫⁻ y in dyCell p.1.1 p.1.2, w y :=
        ENNReal.tsum_mul_left.symm
    _ ≤ ∑' p : {q : ℤ × ℤ // q ∈ czMax ψ c},
          ∫⁻ y in dyCell p.1.1 p.1.2, ψ y * dyMax w y := ENNReal.tsum_le_tsum hcell
    _ = ∫⁻ x in ⋃ p : {q : ℤ × ℤ // q ∈ czMax ψ c}, dyCell p.1.1 p.1.2, ψ x * dyMax w x :=
        (lintegral_iUnion hmeas hdisj (fun x => ψ x * dyMax w x)).symm
    _ = ∫⁻ x in {x : ℝ | c < dyMax ψ x}, ψ x * dyMax w x := by rw [hEeq]

/-- **The weighted Calderón--Zygmund (Cotlar) inequality for the dyadic maximal function**:
`∫ (dyMax ψ)² w ≤ 4 ∫ ψ (dyMax ψ) (dyMax w)`. -/
theorem dyMaxWeightedCZ {ψ w : ℝ → ℝ≥0∞} (hψm : Measurable ψ) (hwm : Measurable w)
    (hψ : ∫⁻ x, ψ x < ⊤) :
    ∫⁻ x, (dyMax ψ x) ^ (2 : ℝ) * w x
      ≤ 4 * ∫⁻ x, ψ x * dyMax ψ x * dyMax w x := by
  have hCZ : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * ∫⁻ x in {x : ℝ | ENNReal.ofReal t < dyMax ψ x}, w x
        ≤ ∫⁻ x in {x : ℝ | ENNReal.ofReal t < dyMax ψ x}, ψ x * dyMax w x :=
    fun t ht => czWeighted (ENNReal.ofReal_pos.mpr ht) hψ
  have hgm : Measurable fun x => (dyMax ψ x) ^ (2:ℝ) :=
    (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp (dyMax_measurable ψ)
  -- the layer cake with respect to the weighted measure
  have hlayer := lintegral_rpow_enorm_eq_layercake (ν := volume.withDensity w) (p := 2)
    (g := dyMax ψ) (by norm_num) (hg := (dyMax_measurable ψ).aemeasurable)
  have h2 : ∫⁻ x, (dyMax ψ x) ^ (2:ℝ) ∂(volume.withDensity w)
      = 2 * ∫⁻ t in Set.Ioi (0:ℝ),
          (∫⁻ x in {x : ℝ | ENNReal.ofReal t < dyMax ψ x}, w x) * ENNReal.ofReal t := by
    have hh : (∫⁻ x, (dyMax ψ x) ^ (2:ℝ) ∂(volume.withDensity w))
        = ∫⁻ x, (dyMax ψ x).rpow (2:ℝ) ∂(volume.withDensity w) := rfl
    rw [hh, hlayer]
    congr 1
    · norm_num
    · refine lintegral_congr fun t => ?_
      rw [withDensity_apply' w {x : ℝ | ENNReal.ofReal t < dyMax ψ x},
        show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  have h3 : ∫⁻ t in Set.Ioi (0:ℝ),
        (∫⁻ x in {x : ℝ | ENNReal.ofReal t < dyMax ψ x}, w x) * ENNReal.ofReal t
      ≤ ∫⁻ t in Set.Ioi (0:ℝ),
        (∫⁻ x in {x : ℝ | ENNReal.ofReal t < dyMax ψ x}, ψ x * dyMax w x) := by
    rw [← lintegral_indicator measurableSet_Ioi
          (fun t => (∫⁻ x in {x : ℝ | ENNReal.ofReal t < dyMax ψ x}, w x) * ENNReal.ofReal t),
      ← lintegral_indicator measurableSet_Ioi
          (fun t => ∫⁻ x in {x : ℝ | ENNReal.ofReal t < dyMax ψ x}, ψ x * dyMax w x)]
    refine lintegral_mono fun t => ?_
    by_cases ht : t ∈ Set.Ioi (0:ℝ)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      exact (mul_comm _ _).trans_le (hCZ t ht)
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  have h4 : ∫⁻ t in Set.Ioi (0:ℝ),
        (∫⁻ x in {x : ℝ | ENNReal.ofReal t < dyMax ψ x}, ψ x * dyMax w x)
      = ∫⁻ x, dyMax ψ x * (ψ x * dyMax w x) := by
    have hstep1 : ∀ t, ∫⁻ x in {x : ℝ | ENNReal.ofReal t < dyMax ψ x}, ψ x * dyMax w x
        = ∫⁻ x, if ENNReal.ofReal t < dyMax ψ x then ψ x * dyMax w x else 0 := by
      intro t
      rw [← lintegral_indicator (measurableSet_lt measurable_const (dyMax_measurable ψ))
        (fun x => ψ x * dyMax w x)]
      refine lintegral_congr fun x => ?_
      by_cases h : ENNReal.ofReal t < dyMax ψ x
      · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | ENNReal.ofReal t < dyMax ψ x} from h),
          if_pos h]
      · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | ENNReal.ofReal t < dyMax ψ x} from h),
          if_neg h]
    have hstep2 : ∫⁻ t in Set.Ioi (0:ℝ),
          (∫⁻ x, if ENNReal.ofReal t < dyMax ψ x then ψ x * dyMax w x else 0)
        = ∫⁻ t, ∫⁻ x, (Set.Ioi (0:ℝ)).indicator
            (fun t => if ENNReal.ofReal t < dyMax ψ x then ψ x * dyMax w x else 0) t := by
      rw [← lintegral_indicator measurableSet_Ioi
        (fun t => ∫⁻ x, if ENNReal.ofReal t < dyMax ψ x then ψ x * dyMax w x else 0)]
      refine lintegral_congr fun t => ?_
      by_cases ht : t ∈ Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem ht]
        rw [show (fun x => (Set.Ioi (0:ℝ)).indicator
            (fun t => if ENNReal.ofReal t < dyMax ψ x then ψ x * dyMax w x else 0) t)
            = fun x => (if ENNReal.ofReal t < dyMax ψ x then ψ x * dyMax w x else 0) from by
              funext x
              rw [Set.indicator_of_mem ht]]
      · rw [Set.indicator_of_notMem ht]
        have hzero : (fun x => (Set.Ioi (0:ℝ)).indicator
            (fun t => if ENNReal.ofReal t < dyMax ψ x then ψ x * dyMax w x else 0) t)
            = fun _ => (0:ℝ≥0∞) := by
          funext x
          rw [Set.indicator_of_notMem ht]
        rw [hzero, lintegral_zero]
    have hunc : Measurable (Function.uncurry (fun t x => (Set.Ioi (0:ℝ)).indicator
        (fun t => if ENNReal.ofReal t < dyMax ψ x then ψ x * dyMax w x else 0) t)) := by
      have heq : Function.uncurry (fun t x => (Set.Ioi (0:ℝ)).indicator
          (fun t => if ENNReal.ofReal t < dyMax ψ x then ψ x * dyMax w x else 0) t)
          = fun p : ℝ × ℝ => if p.1 ∈ Set.Ioi (0:ℝ)
              then (if ENNReal.ofReal p.1 < dyMax ψ p.2 then ψ p.2 * dyMax w p.2 else 0)
              else 0 := by
        funext p
        rw [Function.uncurry_apply_pair, Set.indicator_apply]
      rw [heq]
      refine Measurable.ite ?_ ?_ measurable_const
      · exact measurableSet_Ioi.preimage measurable_fst
      · refine Measurable.ite ?_ ?_ measurable_const
        · exact measurableSet_lt (ENNReal.continuous_ofReal.measurable.comp measurable_fst)
            ((dyMax_measurable ψ).comp measurable_snd)
        · exact (hψm.comp measurable_snd).mul ((dyMax_measurable w).comp measurable_snd)
    simp only [hstep1]
    rw [hstep2, lintegral_lintegral_swap hunc.aemeasurable]
    refine lintegral_congr fun x => ?_
    have hpt : ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
        (fun t => if ENNReal.ofReal t < dyMax ψ x then ψ x * dyMax w x else 0) t
        = ∫⁻ t in Set.Ioi (0:ℝ),
          (if ENNReal.ofReal t < dyMax ψ x then ψ x * dyMax w x else 0) :=
      lintegral_indicator measurableSet_Ioi _
    rw [hpt, lintegral_Ioi_if_lt (dyMax ψ x) (ψ x * dyMax w x), mul_comm]
  have h5 : ∫⁻ x, (dyMax ψ x) ^ (2:ℝ) * w x
      = ∫⁻ x, (dyMax ψ x) ^ (2:ℝ) ∂(volume.withDensity w) := by
    rw [lintegral_withDensity_eq_lintegral_mul volume hwm hgm]
    refine lintegral_congr fun x => ?_
    rw [Pi.mul_apply, mul_comm]
  rw [h5, h2]
  calc 2 * ∫⁻ t in Set.Ioi (0:ℝ),
        (∫⁻ x in {x : ℝ | ENNReal.ofReal t < dyMax ψ x}, w x) * ENNReal.ofReal t
      ≤ 2 * ∫⁻ t in Set.Ioi (0:ℝ),
        (∫⁻ x in {x : ℝ | ENNReal.ofReal t < dyMax ψ x}, ψ x * dyMax w x) :=
        mul_le_mul_right h3 2
    _ = 2 * ∫⁻ x, dyMax ψ x * (ψ x * dyMax w x) := by rw [h4]
    _ = 2 * ∫⁻ x, ψ x * dyMax ψ x * dyMax w x := by
        congr 1
        refine lintegral_congr fun x => ?_
        ac_rfl
    _ ≤ 4 * ∫⁻ x, ψ x * dyMax ψ x * dyMax w x :=
        mul_le_mul_left (by norm_num : (2:ℝ≥0∞) ≤ 4) _

/-! ### The main estimate for bounded families in `L¹` -/

/-- **The `ℓ²`-valued dyadic maximal inequality for `p > 2`** (the bounded, `L¹` case): the
constant is uniform in the number `n` of components. -/
theorem ell2MaxLpGtTwo_bdd {p : ℝ} (hp : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ) (B : ℝ), (∀ t, Measurable (f t)) →
      (∀ t y, |f t y| ≤ B) → (∀ t, ∫⁻ y, ‖f t y‖ₑ < ⊤) →
      ∫⁻ x, (ell2Max f x) ^ (p / 2) ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, (ell2Sq f x) ^ (p / 2) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  have hp2 : 0 < p - 2 := by linarith
  have hq1 : (1 : ℝ) < p / (p - 2) := by
    rw [lt_div_iff₀ hp2]; linarith
  obtain ⟨K, hKpos, hKbd⟩ := dyMaxStrongTypeENNReal (q := p / (p - 2)) hq1
  obtain ⟨K', hK'pos, hK'bd⟩ := dyMaxStrongTypeENNReal (q := p) hp1
  refine ⟨4 * K, by positivity, ?_⟩
  intro n f B hf hbdd hL1
  have hφbdd : ∀ t y, ‖f t y‖ₑ ≤ ENNReal.ofReal B := fun t y => by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hbdd t y)
  have hφfin : ∀ t y, ‖f t y‖ₑ ≠ ⊤ := fun t y => by
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_ne_top
  have hdybdd : ∀ t x, dyMax (fun y => ‖f t y‖ₑ) x ≤ ENNReal.ofReal B := fun t x =>
    (dyMax_le_iSup _ x).trans (iSup_le fun y => hφbdd t y)
  have hdyfin : ∀ t x, dyMax (fun y => ‖f t y‖ₑ) x < ⊤ := fun t x =>
    lt_of_le_of_lt (hdybdd t x) ENNReal.ofReal_lt_top
  -- `φ_t ∈ L^p`, from `φ_t ≤ B` and `φ_t ∈ L^1`
  have hφp : ∀ t, ∫⁻ y, ‖f t y‖ₑ ^ p < ⊤ := by
    intro t
    have h1 : ∀ y, ‖f t y‖ₑ ^ p ≤ ‖f t y‖ₑ * (ENNReal.ofReal B) ^ (p - 1) := by
      intro y
      calc ‖f t y‖ₑ ^ p
          = ‖f t y‖ₑ ^ (1:ℝ) * ‖f t y‖ₑ ^ (p - 1) := by
            conv_lhs => rw [show p = 1 + (p - 1) by ring]
            rw [ENNReal.rpow_add_of_nonneg 1 (p - 1) zero_le_one
              (by linarith : (0:ℝ) ≤ p - 1)]
        _ = ‖f t y‖ₑ * ‖f t y‖ₑ ^ (p - 1) := by rw [ENNReal.rpow_one]
        _ ≤ ‖f t y‖ₑ * (ENNReal.ofReal B) ^ (p - 1) :=
            mul_le_mul_right (ENNReal.rpow_le_rpow (hφbdd t y) (by linarith : (0:ℝ) ≤ p - 1)) _
    calc ∫⁻ y, ‖f t y‖ₑ ^ p
        ≤ ∫⁻ y, ‖f t y‖ₑ * (ENNReal.ofReal B) ^ (p - 1) := lintegral_mono h1
      _ = (∫⁻ y, ‖f t y‖ₑ) * (ENNReal.ofReal B) ^ (p - 1) :=
          lintegral_mul_const _ (hf t).enorm
      _ < ⊤ := ENNReal.mul_lt_top (hL1 t)
          (ENNReal.rpow_lt_top_of_nonneg (by linarith : (0:ℝ) ≤ p - 1) ENNReal.ofReal_ne_top)
  have hdyp : ∀ t, ∫⁻ x, (dyMax (fun y => ‖f t y‖ₑ) x) ^ p < ⊤ := by
    intro t
    exact lt_of_le_of_lt (hK'bd (fun y => ‖f t y‖ₑ) (hf t).enorm (hφfin t))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hφp t))
  have hAfin : ∫⁻ x, (ell2Max f x) ^ (p / 2) < ⊤ := lintegral_ell2Max_lt_top hp hdyp
  -- boundedness of `ell2F`
  have hFF : ∀ x, ell2F f x < ⊤ := by
    intro x
    rw [ell2F, ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < 1/2)]
    exact ENNReal.sum_lt_top.mpr fun t _ =>
      ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (ne_of_lt (lt_of_le_of_lt (hdybdd t x) ENNReal.ofReal_lt_top))
  have hFfin : ∀ x, ell2F f x ≠ ⊤ := fun x => (hFF x).ne
  -- notation
  set A : ℝ≥0∞ := ∫⁻ x, (ell2Max f x) ^ (p / 2) with hA
  set Bs : ℝ≥0∞ := ∫⁻ x, (ell2Sigma f x) ^ p with hBs
  set w : ℝ → ℝ≥0∞ := fun x => (ell2F f x) ^ (p - 2) with hw
  have hFmeas : Measurable (ell2F f) := ell2F_measurable
  have hσmeas : Measurable (ell2Sigma f) := ell2Sigma_measurable hf
  have hwmeas : Measurable w := by
    rw [hw]; exact (ENNReal.continuous_rpow_const (y := p - 2)).measurable.comp hFmeas
  have hdwmeas : Measurable (dyMax w) := dyMax_measurable w
  have hwfin : ∀ x, w x ≠ ⊤ := by
    intro x
    rw [hw]
    exact ENNReal.rpow_ne_top_of_nonneg (by linarith : (0:ℝ) ≤ p - 2) (hFfin x)
  have hmain : A ≤ 4 * ENNReal.ofReal K * Bs ^ (1/p) * A ^ ((p-1)/p) := by
    have h1 : A = ∫⁻ x, ell2Max f x * w x := by
      rw [hA, hw]
      refine lintegral_congr fun x => ?_
      rw [rpow_eq_rpow_mul_rpow_sub (show (0:ℝ) < 1 by norm_num)
        (by linarith : (1:ℝ) ≤ p / 2), ENNReal.rpow_one]
      congr 1
      rw [show p / 2 - 1 = (p - 2) / 2 by ring]
      simp only [ell2F]
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    have h2 : ∫⁻ x, ell2Max f x * w x
        = ∑ t : Fin n, ∫⁻ x, (dyMax (fun y => ‖f t y‖ₑ) x) ^ (2:ℝ) * w x := by
      have hfun : (fun x => ell2Max f x * w x)
          = fun x => ∑ t : Fin n, (dyMax (fun y => ‖f t y‖ₑ) x) ^ (2:ℝ) * w x := by
        funext x
        rw [ell2Max, Finset.sum_mul]
      rw [hfun, lintegral_finsetSum]
      intro t _
      exact ((ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp
        (dyMax_measurable _)).mul hwmeas
    have h3 : ∑ t : Fin n, ∫⁻ x, (dyMax (fun y => ‖f t y‖ₑ) x) ^ (2:ℝ) * w x
        ≤ ∑ t : Fin n, 4 * ∫⁻ x, ‖f t x‖ₑ * dyMax (fun y => ‖f t y‖ₑ) x * dyMax w x :=
      Finset.sum_le_sum fun t _ => dyMaxWeightedCZ ((hf t).enorm) hwmeas (hL1 t)
    have h4 : ∑ t : Fin n, 4 * ∫⁻ x, ‖f t x‖ₑ * dyMax (fun y => ‖f t y‖ₑ) x * dyMax w x
        = 4 * ∫⁻ x, (∑ t : Fin n, ‖f t x‖ₑ * dyMax (fun y => ‖f t y‖ₑ) x) * dyMax w x := by
      rw [← Finset.mul_sum, ← lintegral_finsetSum]
      · congr 1
        refine lintegral_congr fun x => ?_
        rw [Finset.sum_mul]
      · intro t _
        exact ((hf t).enorm.mul (dyMax_measurable _)).mul hdwmeas
    have h5 : 4 * ∫⁻ x, (∑ t : Fin n, ‖f t x‖ₑ * dyMax (fun y => ‖f t y‖ₑ) x) * dyMax w x
        ≤ 4 * ∫⁻ x, ell2Sigma f x * ell2F f x * dyMax w x := by
      refine mul_le_mul_right ?_ 4
      refine lintegral_mono fun x => ?_
      refine mul_le_mul_left ?_ _
      exact ENNReal_sum_mul_le_sqrt_mul_sqrt (fun t => ‖f t x‖ₑ)
        (fun t => dyMax (fun y => ‖f t y‖ₑ) x)
    have h6 : 4 * ∫⁻ x, ell2Sigma f x * ell2F f x * dyMax w x
        ≤ 4 * ((∫⁻ x, (ell2Sigma f x) ^ p) ^ (1/p) * (∫⁻ x, (ell2F f x) ^ p) ^ (1/p)
            * (∫⁻ x, (dyMax w x) ^ (p/(p-2))) ^ ((p-2)/p)) :=
      mul_le_mul_right (lintegral_mul_mul_le hp hσmeas.aemeasurable hFmeas.aemeasurable
        hdwmeas.aemeasurable) 4
    -- the weight's `L^{p'}` norm
    have hX : (∫⁻ x, (dyMax w x) ^ (p/(p-2))) ^ ((p-2)/p)
        ≤ ENNReal.ofReal K * (∫⁻ x, (ell2F f x) ^ p) ^ ((p-2)/p) := by
      have hKb := hKbd w hwmeas hwfin
      have hwq : ∫⁻ x, w x ^ (p/(p-2)) = ∫⁻ x, (ell2F f x) ^ p := by
        refine lintegral_congr fun x => ?_
        rw [hw, ← ENNReal.rpow_mul]
        congr 1
        have hne : (p : ℝ) ≠ 0 := by linarith
        have hne2 : (p - 2 : ℝ) ≠ 0 := by linarith
        field_simp
      have hKq : (ENNReal.ofReal (K ^ (p/(p-2)))) ^ ((p-2)/p) = ENNReal.ofReal K := by
        rw [ENNReal.ofReal_rpow_of_nonneg (x := K ^ (p/(p-2))) (by positivity) (by positivity)]
        congr 1
        rw [← Real.rpow_mul hKpos.le]
        rw [show (p / (p - 2)) * ((p - 2) / p) = 1 by
          have hne : (p : ℝ) ≠ 0 := by linarith
          have hne2 : (p - 2 : ℝ) ≠ 0 := by linarith
          field_simp]
        exact Real.rpow_one K
      calc (∫⁻ x, (dyMax w x) ^ (p/(p-2))) ^ ((p-2)/p)
          ≤ (ENNReal.ofReal (K ^ (p/(p-2))) * ∫⁻ x, w x ^ (p/(p-2))) ^ ((p-2)/p) :=
            ENNReal.rpow_le_rpow hKb (by positivity)
        _ = (ENNReal.ofReal (K ^ (p/(p-2))) * ∫⁻ x, (ell2F f x) ^ p) ^ ((p-2)/p) := by
            rw [hwq]
        _ = ENNReal.ofReal K * (∫⁻ x, (ell2F f x) ^ p) ^ ((p-2)/p) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), hKq]
    have hAeq : (∫⁻ x, (ell2F f x) ^ p) = A := by
      rw [hA]
      refine lintegral_congr fun x => ?_
      simp only [ell2F]
      exact rpow_half_rpow _ p
    have hAA : A ^ (1/p) * A ^ ((p-2)/p) = A ^ ((p-1)/p) := by
      rw [← ENNReal.rpow_add_of_nonneg (1/p) ((p-2)/p) (by positivity) (by positivity)]
      congr 1
      ring
    calc A = ∫⁻ x, ell2Max f x * w x := h1
      _ = ∑ t : Fin n, ∫⁻ x, (dyMax (fun y => ‖f t y‖ₑ) x) ^ (2:ℝ) * w x := h2
      _ ≤ ∑ t : Fin n, 4 * ∫⁻ x, ‖f t x‖ₑ * dyMax (fun y => ‖f t y‖ₑ) x * dyMax w x := h3
      _ = 4 * ∫⁻ x, (∑ t : Fin n, ‖f t x‖ₑ * dyMax (fun y => ‖f t y‖ₑ) x) * dyMax w x := h4
      _ ≤ 4 * ∫⁻ x, ell2Sigma f x * ell2F f x * dyMax w x := h5
      _ ≤ 4 * ((∫⁻ x, (ell2Sigma f x) ^ p) ^ (1/p) * (∫⁻ x, (ell2F f x) ^ p) ^ (1/p)
            * (∫⁻ x, (dyMax w x) ^ (p/(p-2))) ^ ((p-2)/p)) := h6
      _ ≤ 4 * (Bs ^ (1/p) * A ^ (1/p) * (ENNReal.ofReal K * A ^ ((p-2)/p))) := by
          refine mul_le_mul_right ?_ 4
          rw [← hBs, hAeq]
          rw [hAeq] at hX
          exact mul_le_mul_of_nonneg_left hX (by positivity)
      _ = 4 * ENNReal.ofReal K * Bs ^ (1/p) * A ^ ((p-1)/p) := by
          rw [show 4 * (Bs ^ (1/p) * A ^ (1/p) * (ENNReal.ofReal K * A ^ ((p-2)/p)))
              = 4 * (Bs ^ (1/p) * ENNReal.ofReal K * (A ^ (1/p) * A ^ ((p-2)/p))) by
            ac_rfl]
          rw [hAA]
          ac_rfl
  -- the division
  by_cases hA0 : A = 0
  · rw [hA0]
    positivity
  · have hApos : 0 < A := zero_lt_iff.mpr hA0
    have hAtop : A ≠ ⊤ := lt_top_iff_ne_top.mp (by rw [hA]; exact hAfin)
    have h1p : (0:ℝ) < 1/p := by positivity
    have hpp : (0:ℝ) < (p-1)/p := by positivity
    have hkey : A ^ (1/p) * A ^ ((p-1)/p)
        ≤ (4 * ENNReal.ofReal K * Bs ^ (1/p)) * A ^ ((p-1)/p) := by
      rw [← ENNReal.rpow_add_of_nonneg (1/p) ((p-1)/p) h1p.le hpp.le,
        show (1:ℝ)/p + (p-1)/p = 1 by field_simp; ring, ENNReal.rpow_one]
      exact hmain
    have hvpos : A ^ ((p-1)/p) ≠ 0 := (ENNReal.rpow_pos hApos hAtop).ne'
    have hvt : A ^ ((p-1)/p) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hpp.le hAtop
    have hkey2 : A ^ (1/p) ≤ 4 * ENNReal.ofReal K * Bs ^ (1/p) :=
      (ENNReal.mul_le_mul_iff_left hvpos hvt).mp hkey
    have hraise : (A ^ (1/p)) ^ p ≤ (4 * ENNReal.ofReal K * Bs ^ (1/p)) ^ p :=
      ENNReal.rpow_le_rpow hkey2 hp0.le
    have hL : (A ^ (1/p)) ^ p = A := by
      rw [← ENNReal.rpow_mul, one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
    have h4K : (4:ℝ≥0∞) ^ p * (ENNReal.ofReal K) ^ p = ENNReal.ofReal ((4 * K) ^ p) := by
      rw [show (4:ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0:ℝ) ≤ 4) hp0.le,
        ENNReal.ofReal_rpow_of_nonneg hKpos.le hp0.le,
        ← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (by norm_num) hKpos.le]
    have hR : (4 * ENNReal.ofReal K * Bs ^ (1/p)) ^ p = ENNReal.ofReal ((4 * K) ^ p) * Bs := by
      calc (4 * ENNReal.ofReal K * Bs ^ (1/p)) ^ p
          = (4 * ENNReal.ofReal K) ^ p * (Bs ^ (1/p)) ^ p := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        _ = 4 ^ p * (ENNReal.ofReal K) ^ p * Bs := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul,
              one_div_mul_cancel hp0.ne', ENNReal.rpow_one]
        _ = ENNReal.ofReal ((4 * K) ^ p) * Bs := by rw [h4K]
    rw [hL, hR] at hraise
    refine hraise.trans (le_of_eq ?_)
    congr 1
    rw [hBs]
    refine lintegral_congr fun x => ?_
    simp only [ell2Sigma]
    exact rpow_half_rpow _ p


/-! ### Truncation of a family of functions -/

/-- The `N`-th truncation of a family of functions: the values are kept only where both the value
and the argument are bounded by `N`. -/
noncomputable def truncF {n : ℕ} (N : ℕ) (f : Fin n → ℝ → ℝ) : Fin n → ℝ → ℝ :=
  fun t y => if |f t y| ≤ (N : ℝ) ∧ |y| ≤ (N : ℝ) then f t y else 0

lemma truncF_measurable {n : ℕ} (N : ℕ) {f : Fin n → ℝ → ℝ} (hf : ∀ t, Measurable (f t)) :
    ∀ t, Measurable (truncF N f t) := by
  intro t
  have hset : MeasurableSet {y : ℝ | |f t y| ≤ (N:ℝ) ∧ |y| ≤ (N:ℝ)} := by
    have h1 : MeasurableSet ((f t) ⁻¹' (Set.Icc (-(N:ℝ)) (N:ℝ))) :=
      measurableSet_Icc.preimage (hf t)
    convert h1.inter (measurableSet_Icc (a := -(N:ℝ)) (b := (N:ℝ))) using 1
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Icc, Set.mem_ofPred_eq, abs_le]
  exact Measurable.ite hset (hf t) measurable_const

lemma truncF_abs_le {n : ℕ} (N : ℕ) (f : Fin n → ℝ → ℝ) (t : Fin n) (y : ℝ) :
    |truncF N f t y| ≤ (N : ℝ) := by
  unfold truncF
  by_cases h : |f t y| ≤ (N:ℝ) ∧ |y| ≤ (N:ℝ)
  · rw [if_pos h]; exact h.1
  · rw [if_neg h]; simp

lemma truncF_norm_eq {n : ℕ} (N : ℕ) (f : Fin n → ℝ → ℝ) (t : Fin n) (y : ℝ) :
    ‖truncF N f t y‖ₑ
      = if |f t y| ≤ (N:ℝ) ∧ |y| ≤ (N:ℝ) then ‖f t y‖ₑ else 0 := by
  unfold truncF
  by_cases h : |f t y| ≤ (N:ℝ) ∧ |y| ≤ (N:ℝ) <;> simp [h]

lemma truncF_norm_le {n : ℕ} (N : ℕ) (f : Fin n → ℝ → ℝ) (t : Fin n) (y : ℝ) :
    ‖truncF N f t y‖ₑ ≤ ‖f t y‖ₑ := by
  rw [truncF_norm_eq]
  by_cases h : |f t y| ≤ (N:ℝ) ∧ |y| ≤ (N:ℝ) <;> simp [h]

lemma truncF_norm_mono {n : ℕ} {N M : ℕ} (hNM : N ≤ M) (f : Fin n → ℝ → ℝ) (t : Fin n) (y : ℝ) :
    ‖truncF N f t y‖ₑ ≤ ‖truncF M f t y‖ₑ := by
  rw [truncF_norm_eq, truncF_norm_eq]
  have hNM' : (N:ℝ) ≤ (M:ℝ) := by exact_mod_cast hNM
  by_cases h : |f t y| ≤ (N:ℝ) ∧ |y| ≤ (N:ℝ)
  · have h' : |f t y| ≤ (M:ℝ) ∧ |y| ≤ (M:ℝ) := ⟨le_trans h.1 hNM', le_trans h.2 hNM'⟩
    rw [if_pos h, if_pos h']
  · rw [if_neg h]
    split_ifs with h2
    · exact zero_le
    · exact le_refl _

lemma iSup_truncF_norm {n : ℕ} (f : Fin n → ℝ → ℝ) (t : Fin n) (y : ℝ) :
    (⨆ N, ‖truncF N f t y‖ₑ) = ‖f t y‖ₑ := by
  refine le_antisymm (iSup_le fun N => truncF_norm_le N f t y) ?_
  obtain ⟨M, hM⟩ : ∃ M : ℕ, |f t y| ≤ (M:ℝ) ∧ |y| ≤ (M:ℝ) := by
    refine ⟨⌈max |f t y| |y|⌉₊, ?_, ?_⟩
    · exact le_trans (le_max_left _ _) (Nat.le_ceil _)
    · exact le_trans (le_max_right _ _) (Nat.le_ceil _)
  calc ‖f t y‖ₑ = ‖truncF M f t y‖ₑ := by rw [truncF_norm_eq, if_pos hM]
    _ ≤ ⨆ N, ‖truncF N f t y‖ₑ := le_iSup (fun N => ‖truncF N f t y‖ₑ) M

lemma lintegral_truncF_norm_lt_top {n : ℕ} (N : ℕ) (f : Fin n → ℝ → ℝ) (t : Fin n) :
    ∫⁻ y, ‖truncF N f t y‖ₑ < ⊤ := by
  have h1 : ∀ y, ‖truncF N f t y‖ₑ ≤ ENNReal.ofReal (N:ℝ) * (Set.Icc (-(N:ℝ)) (N:ℝ)).indicator
      (fun _ => (1:ℝ≥0∞)) y := by
    intro y
    rw [truncF_norm_eq]
    by_cases h : |f t y| ≤ (N:ℝ) ∧ |y| ≤ (N:ℝ)
    · rw [if_pos h, Set.indicator_of_mem, mul_one]
      · rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal h.1
      · rw [Set.mem_Icc]; exact abs_le.mp h.2
    · rw [if_neg h]
      exact zero_le
  calc ∫⁻ y, ‖truncF N f t y‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal (N:ℝ) * (Set.Icc (-(N:ℝ)) (N:ℝ)).indicator
          (fun _ => (1:ℝ≥0∞)) y := lintegral_mono h1
    _ = ENNReal.ofReal (N:ℝ) * ∫⁻ y, (Set.Icc (-(N:ℝ)) (N:ℝ)).indicator
          (fun _ => (1:ℝ≥0∞)) y := by
        rw [lintegral_const_mul _ (measurable_const.indicator measurableSet_Icc)]
    _ = ENNReal.ofReal (N:ℝ) * volume (Set.Icc (-(N:ℝ)) (N:ℝ)) := by
        rw [lintegral_indicator measurableSet_Icc (f := fun _ => (1:ℝ≥0∞)), setLIntegral_const,
          one_mul]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by
        rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

lemma ell2Sq_truncF_le {n : ℕ} (N : ℕ) (f : Fin n → ℝ → ℝ) (y : ℝ) :
    ell2Sq (truncF N f) y ≤ ell2Sq f y := by
  unfold ell2Sq
  exact Finset.sum_le_sum fun t _ => ENNReal.rpow_le_rpow (truncF_norm_le N f t y) (by norm_num)

lemma ell2Max_truncF_mono {n : ℕ} {N M : ℕ} (hNM : N ≤ M) (f : Fin n → ℝ → ℝ) (x : ℝ) :
    ell2Max (truncF N f) x ≤ ell2Max (truncF M f) x := by
  unfold ell2Max
  exact Finset.sum_le_sum fun t _ => ENNReal.rpow_le_rpow
    (dyMax_mono (fun y => truncF_norm_mono hNM f t y) x) (by norm_num)

lemma iSup_ell2Max_truncF {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : ∀ t, Measurable (f t)) (x : ℝ) :
    ell2Max f x = ⨆ N, ell2Max (truncF N f) x := by
  have hmono : ∀ t, Monotone fun N => (dyMax (fun y => ‖truncF N f t y‖ₑ) x) ^ (2:ℝ) :=
    fun t a b hab => ENNReal.rpow_le_rpow
      (dyMax_mono (fun y => truncF_norm_mono hab f t y) x) (by norm_num)
  have hsup : ∀ t, (⨆ N, dyMax (fun y => ‖truncF N f t y‖ₑ) x) = dyMax (fun y => ‖f t y‖ₑ) x := by
    intro t
    have key := dyMax_iSup (ψ := fun N y => ‖truncF N f t y‖ₑ)
      (fun N => (truncF_measurable N hf t).enorm) (fun a b hab y => truncF_norm_mono hab f t y)
    rw [show (fun y => ⨆ N, ‖truncF N f t y‖ₑ) = fun y => ‖f t y‖ₑ from
      funext fun y => iSup_truncF_norm f t y] at key
    exact congrFun key.symm x
  have hsum : (⨆ N, ell2Max (truncF N f) x) = ∑ t : Fin n, (dyMax (fun y => ‖f t y‖ₑ) x) ^ (2:ℝ) := by
    have hfun : ∀ N, ell2Max (truncF N f) x
        = ∑ t, (dyMax (fun y => ‖truncF N f t y‖ₑ) x) ^ (2:ℝ) := by
      intro N; rw [ell2Max]
    simp only [hfun]
    rw [iSup_finset_sum_eq hmono]
    exact Finset.sum_congr rfl fun t _ => by
      rw [← iSup_rpow_eq (fun a b hab => dyMax_mono (fun y => truncF_norm_mono hab f t y) x)
        (by norm_num : (0:ℝ) ≤ 2), hsup t]
  rw [ell2Max]
  exact hsum.symm

theorem ell2MaxLpGtTwo {p : ℝ} (hp : 2 < p) : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) → ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Max f x) ^ (p / 2) ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, (Work.BourgainPlan.Maximal.ell2Sq f x) ^ (p / 2) := by
  obtain ⟨C, hCpos, hC⟩ := ell2MaxLpGtTwo_bdd hp
  refine ⟨C, hCpos, fun n f hf => ?_⟩
  have hN : ∀ N, ∫⁻ x, (ell2Max (truncF N f) x) ^ (p/2)
      ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, (ell2Sq f x) ^ (p/2) := by
    intro N
    refine (hC n (truncF N f) (N:ℝ) (truncF_measurable N hf) (truncF_abs_le N f)
      (lintegral_truncF_norm_lt_top N f)).trans ?_
    refine mul_le_mul_right ?_ _
    exact lintegral_mono fun x => ENNReal.rpow_le_rpow (ell2Sq_truncF_le N f x) (by positivity)
  have hpt : ∀ x, (ell2Max f x) ^ (p/2) = ⨆ N, (ell2Max (truncF N f) x) ^ (p/2) := by
    intro x
    rw [iSup_ell2Max_truncF f hf x, iSup_rpow_eq (fun a b hab => ell2Max_truncF_mono hab f x)
      (by positivity)]
  have hmeas : ∀ N, Measurable fun x => (ell2Max (truncF N f) x) ^ (p/2) := fun N =>
    (ENNReal.continuous_rpow_const (y := p/2)).measurable.comp (ell2Max_measurable _)
  have hmonoN : Monotone fun N => fun x => (ell2Max (truncF N f) x) ^ (p/2) :=
    fun a b hab x => ENNReal.rpow_le_rpow (ell2Max_truncF_mono hab f x) (by positivity)
  calc ∫⁻ x, (ell2Max f x) ^ (p/2)
      = ∫⁻ x, ⨆ N, (ell2Max (truncF N f) x) ^ (p/2) := lintegral_congr hpt
    _ = ⨆ N, ∫⁻ x, (ell2Max (truncF N f) x) ^ (p/2) := lintegral_iSup hmeas hmonoN
    _ ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, (ell2Sq f x) ^ (p/2) := iSup_le hN

end Work.BourgainPlan.Maximal
