import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmPotential_iteratedFDeriv
import Submission.Work.CR.Flat.Cauchy.fderiv_bmPotential
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

noncomputable section

open scoped NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace Work.CR.Flat.Cauchy

open Work.CR.Flat

/-! ## Elementary analytic lemmas -/

/-- The zeroth iterated derivative is the function itself, up to the canonical linear isometry
`F ≃ ((Fin 0 → E) [×0]→L[ℝ] F)`; hence the difference of two zeroth derivatives is the
difference of the values. -/
private lemma norm_iteratedFDerivWithin_zero_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (s : Set E) (x y : E) :
    ‖iteratedFDerivWithin ℝ 0 g s x - iteratedFDerivWithin ℝ 0 g s y‖ = ‖g x - g y‖ := by
  have hAB : ∀ A B : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) F, ‖A - B‖ = ‖A 0 - B 0‖ := by
    intro A B
    refine le_antisymm ?_ ?_
    · refine ContinuousMultilinearMap.opNorm_le_bound (f := A - B) (norm_nonneg _) fun v => ?_
      have hv : v = 0 := Subsingleton.elim v 0
      rw [hv, sub_apply]
      simp
    · have h := (A - B).le_opNorm (0 : Fin 0 → E)
      rw [sub_apply] at h
      simpa using h
  rw [hAB, iteratedFDerivWithin_zero_apply, iteratedFDerivWithin_zero_apply]

/-- A continuous multilinear map whose values are all bounded by `Φ · ∏ i, ‖v i‖` has operator
norm at most `Φ`. -/
lemma ofReal_opNorm_le_of_bound_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {G : Type*} [SeminormedAddCommGroup G] [NormedSpace ℝ G]
    (f : ContinuousMultilinearMap ℝ E G) {Φ : ℝ≥0∞}
    (h : ∀ v : (i : ι) → E i, ENNReal.ofReal ‖f v‖ ≤ Φ * ENNReal.ofReal (∏ i, ‖v i‖)) :
    ENNReal.ofReal ‖f‖ ≤ Φ := by
  rcases eq_or_ne Φ ⊤ with hΦ | hΦ
  · rw [hΦ]; exact le_top
  · have h' : ∀ v, ‖f v‖ ≤ Φ.toReal * ∏ i, ‖v i‖ := fun v => by
      have h1 := h v
      have h2 : (ENNReal.ofReal ‖f v‖).toReal ≤ (Φ * ENNReal.ofReal (∏ i, ‖v i‖)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hΦ ENNReal.ofReal_ne_top) h1
      simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _),
        ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => norm_nonneg _)] using h2
    have hnorm := f.opNorm_le_bound ENNReal.toReal_nonneg h'
    calc ENNReal.ofReal ‖f‖ ≤ ENNReal.ofReal Φ.toReal := ENNReal.ofReal_le_ofReal hnorm
      _ ≤ Φ := ENNReal.ofReal_toReal_le

/-- If `f : ℂⁿ → ℂ` is `C^{k+1}` and `m ≤ k` then `y ↦ D^m f(y)[v]` is `C¹`. -/
lemma contDiff_one_iteratedFDeriv_apply {n k m : ℕ} (hm : m ≤ k)
    {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ (k + 1) f) (v : Fin m → (Fin n → ℂ)) :
    ContDiff ℝ 1 (fun y => iteratedFDeriv ℝ m f y v) :=
  (ContinuousLinearMap.contDiff
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => (Fin n → ℂ)) ℂ v)).comp
    (ContDiff.iteratedFDeriv_right (i := m) (m := 1) (hf)
      (by exact_mod_cast (by omega : 1 + m ≤ k + 1)))

/-- If `g` vanishes off the open polydisc of radii `r / 2`, then every iterated derivative of `g`
vanishes on `{z | ∃ i, r i ≤ ‖z i - c i‖}`; indeed that set is contained in the *interior* of the
vanishing set (the gap between `r i / 2` and `r i` is strict because `r i > 0`), so `g` is
eventually zero near each of its points. -/
lemma bmIter_vanishing {n : ℕ} {c : Fin n → ℂ} {r : Fin n → ℝ} (hr : ∀ j, 0 < r j)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : (Fin n → ℂ) → F}
    (hvan : ∀ z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → g z = 0)
    {m : ℕ} {z : Fin n → ℂ} (hz : ∃ i, r i ≤ ‖z i - c i‖) :
    iteratedFDeriv ℝ m g z = 0 := by
  obtain ⟨i, hi⟩ := hz
  have hmem : g =ᶠ[𝓝 z] (fun _ : Fin n → ℂ => (0 : F)) := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨{w | r i / 2 < ‖w i - c i‖}, ?_, ?_⟩
    · refine IsOpen.mem_nhds ?_ (lt_of_lt_of_le (half_lt_self (hr i)) hi)
      exact isOpen_lt continuous_const (((continuous_apply i).sub continuous_const).norm)
    · intro w hw
      exact hvan w ⟨i, le_of_lt hw⟩
  simpa [iteratedFDeriv_fun_zero] using (hmem.iteratedFDeriv ℝ m).eq_of_nhds

/-- The `C^{0,α}`-norm of `y ↦ D^m f(y)[v]` is bounded by `∏ i, ‖v i‖` times the `C^{k,α}`-norm of
`f` on all of `ℂⁿ`, whenever `m ≤ k`. -/
lemma bmIter_holderNorm_zero_le {n m k : ℕ} (hm : m ≤ k) {α : ℝ}
    {f : (Fin n → ℂ) → ℂ} (v : Fin m → (Fin n → ℂ)) :
    holderNorm 0 α (fun y => iteratedFDeriv ℝ m f y v) Set.univ
      ≤ ENNReal.ofReal (∏ i, ‖v i‖) * holderNorm k α f Set.univ := by
  set Φ : ℝ≥0∞ := ENNReal.ofReal (∏ i, ‖v i‖) with hΦ
  set g : (Fin n → ℂ) → ℂ := fun y => iteratedFDeriv ℝ m f y v with hg
  change holderNorm 0 α g Set.univ ≤ Φ * holderNorm k α f Set.univ
  have ha : iterDerivNorm 0 g Set.univ ≤ Φ * iterDerivNorm m f Set.univ := by
    refine iSup₂_le fun x _ => ?_
    rw [norm_iteratedFDerivWithin_zero]
    calc ENNReal.ofReal ‖g x‖
        ≤ ENNReal.ofReal (‖iteratedFDeriv ℝ m f x‖ * ∏ i, ‖v i‖) :=
          ENNReal.ofReal_le_ofReal (ContinuousMultilinearMap.le_opNorm _ _)
      _ = ENNReal.ofReal ‖iteratedFDeriv ℝ m f x‖ * Φ := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), hΦ]
      _ ≤ iterDerivNorm m f Set.univ * Φ := by
          gcongr
          rw [← iteratedFDerivWithin_univ (n := m) (f := f)]
          exact le_iterDerivNorm m f Set.univ (mem_univ x)
      _ = Φ * iterDerivNorm m f Set.univ := by rw [mul_comm]
  have hb : holderSeminorm 0 α g Set.univ ≤ Φ * holderSeminorm m α f Set.univ := by
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
    rw [norm_iteratedFDerivWithin_zero_sub]
    have hρ : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    have h1 : ‖g x - g y‖
        ≤ ‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ * ∏ i, ‖v i‖ := by
      have heq : g x - g y = (iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y) v := by
        rw [sub_apply]
      rw [heq]
      exact ContinuousMultilinearMap.le_opNorm _ _
    have h2 : ‖g x - g y‖ / ‖x - y‖ ^ α
        ≤ (‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ / ‖x - y‖ ^ α)
            * ∏ i, ‖v i‖ :=
      (div_le_div_of_nonneg_right h1 hρ.le).trans (le_of_eq (by ring))
    calc ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α)
        ≤ ENNReal.ofReal ((‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ / ‖x - y‖ ^ α)
            * ∏ i, ‖v i‖) := ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (‖iteratedFDeriv ℝ m f x - iteratedFDeriv ℝ m f y‖ / ‖x - y‖ ^ α) * Φ := by
          rw [ENNReal.ofReal_mul (div_nonneg (norm_nonneg _) hρ.le), hΦ]
      _ ≤ holderSeminorm m α f Set.univ * Φ := by
          gcongr
          rw [← iteratedFDerivWithin_univ (n := m) (f := f)]
          exact le_holderSeminorm m α f Set.univ (mem_univ x) (mem_univ y) hxy
      _ = Φ * holderSeminorm m α f Set.univ := by rw [mul_comm]
  have h0 : holderNorm 0 α g Set.univ
      = iterDerivNorm 0 g Set.univ + holderSeminorm 0 α g Set.univ := by
    simp [holderNorm]
  have hk : iterDerivNorm m f Set.univ + holderSeminorm m α f Set.univ
      ≤ holderNorm k α f Set.univ := by
    rw [holderNorm]
    exact Finset.single_le_sum
      (f := fun i => iterDerivNorm i f Set.univ + holderSeminorm i α f Set.univ)
      (fun _ _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  rw [h0]
  calc iterDerivNorm 0 g Set.univ + holderSeminorm 0 α g Set.univ
      ≤ Φ * iterDerivNorm m f Set.univ + Φ * holderSeminorm m α f Set.univ := add_le_add ha hb
    _ = Φ * (iterDerivNorm m f Set.univ + holderSeminorm m α f Set.univ) := by rw [mul_add]
    _ ≤ Φ * holderNorm k α f Set.univ := by gcongr

/-! ## The two main estimates -/

/-- **The potential of the `m`-th derivative of the data.**  For data supported in the half-size
polydisc, the `m`-th iterated derivative of the Bochner–Martinelli potential is (by the
commutation identity) the potential of the `m`-th iterated derivative of the data, to which the
order-zero estimate `hC₀` applies. -/
lemma bmPotential_iter_apply_le {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ}
    {α : ℝ} (hr : ∀ j, 0 < r j) {k m : ℕ} (hm : m ≤ k) {C₀ : ℝ}
    (hC₀ : ∀ g : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (g j)) →
      (∀ j z, (∃ i, r i ≤ ‖z i - c i‖) → g j z = 0) →
      holderNorm 1 α (bmPotential g) (polydisc c r)
        ≤ ENNReal.ofReal C₀ * ∑ j, holderNorm 0 α (g j) Set.univ)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, ContDiff ℝ (k + 1) (f j))
    (hsat : ∀ j z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → f j z = 0)
    (v : Fin m → (Fin n → ℂ)) (z : Fin n → ℂ) (hz : z ∈ polydisc c (fun j => r j / 2)) :
    ENNReal.ofReal ‖iteratedFDeriv ℝ m (fun z => bmPotential f z) z v‖
      ≤ ENNReal.ofReal C₀ * (∑ j, holderNorm k α (f j) Set.univ)
          * ENNReal.ofReal (∏ i, ‖v i‖) := by
  set G : Fin n → (Fin n → ℂ) → ℂ := fun j y => iteratedFDeriv ℝ m (f j) y v with hG
  have hGm : ∀ j, ContDiff ℝ m (f j) :=
    fun j => (hf j).of_le (by exact_mod_cast (Nat.le_trans hm (Nat.le_succ k)))
  have hG1 : ∀ j, ContDiff ℝ 1 (G j) := fun j => contDiff_one_iteratedFDeriv_apply hm (hf j) v
  have hGvan : ∀ j y, (∃ i, r i ≤ ‖y i - c i‖) → G j y = 0 := fun j y hy => by
    have h0 : iteratedFDeriv ℝ m (f j) y = 0 :=
      bmIter_vanishing hr (fun w hw => hsat j w hw) hy
    simp [hG, h0]
  have hzfull : z ∈ polydisc c r := polydisc_mono (fun j => by linarith [hr j]) hz
  have hsum : (∑ j, holderNorm 0 α (G j) Set.univ)
      ≤ ENNReal.ofReal (∏ i, ‖v i‖) * (∑ j, holderNorm k α (f j) Set.univ) := by
    calc ∑ j, holderNorm 0 α (G j) Set.univ
        ≤ ∑ j, ENNReal.ofReal (∏ i, ‖v i‖) * holderNorm k α (f j) Set.univ :=
          Finset.sum_le_sum fun j _ => bmIter_holderNorm_zero_le hm v
      _ = ENNReal.ofReal (∏ i, ‖v i‖) * ∑ j, holderNorm k α (f j) Set.univ := by
          rw [Finset.mul_sum]
  have hcomm := bmPotential_iteratedFDeriv hn hr hGm hsat v z
  rw [hcomm]
  change ENNReal.ofReal ‖bmPotential G z‖
      ≤ ENNReal.ofReal C₀ * (∑ j, holderNorm k α (f j) Set.univ)
          * ENNReal.ofReal (∏ i, ‖v i‖)
  calc ENNReal.ofReal ‖bmPotential G z‖
      ≤ holderNorm 1 α (bmPotential G) (polydisc c r) := norm_apply_le_holderNorm 1 α _ _ hzfull
    _ ≤ ENNReal.ofReal C₀ * ∑ j, holderNorm 0 α (G j) Set.univ := hC₀ G hG1 hGvan
    _ ≤ ENNReal.ofReal C₀
          * (ENNReal.ofReal (∏ i, ‖v i‖) * ∑ j, holderNorm k α (f j) Set.univ) := by gcongr
    _ = ENNReal.ofReal C₀ * (∑ j, holderNorm k α (f j) Set.univ)
          * ENNReal.ofReal (∏ i, ‖v i‖) := by ac_rfl

/-- **The potential of the `m`-th derivative of the data, Hölder version.**  The
`α`-Hölder quotient of the `m`-th derivative of the potential is bounded by the `C^{1,α}` bound for
the potential of the `m`-th derivative of the data, with the same data estimate as above. -/
lemma bmPotential_iter_sub_le {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ}
    {α : ℝ} (hr : ∀ j, 0 < r j) {k m : ℕ} (hm : m ≤ k) {C₀ : ℝ}
    (hC₀ : ∀ g : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (g j)) →
      (∀ j z, (∃ i, r i ≤ ‖z i - c i‖) → g j z = 0) →
      holderNorm 1 α (bmPotential g) (polydisc c r)
        ≤ ENNReal.ofReal C₀ * ∑ j, holderNorm 0 α (g j) Set.univ)
    {f : Fin n → (Fin n → ℂ) → ℂ} (hf : ∀ j, ContDiff ℝ (k + 1) (f j))
    (hsat : ∀ j z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → f j z = 0)
    (v : Fin m → (Fin n → ℂ)) (x y : Fin n → ℂ)
    (hx : x ∈ polydisc c (fun j => r j / 2)) (hy : y ∈ polydisc c (fun j => r j / 2))
    (hxy : x ≠ y) :
    ENNReal.ofReal ‖iteratedFDeriv ℝ m (fun z => bmPotential f z) x v
        - iteratedFDeriv ℝ m (fun z => bmPotential f z) y v‖
      ≤ (ENNReal.ofReal C₀ * (∑ j, holderNorm k α (f j) Set.univ)
            * ENNReal.ofReal (‖x - y‖ ^ α)) * ENNReal.ofReal (∏ i, ‖v i‖) := by
  set G : Fin n → (Fin n → ℂ) → ℂ := fun j y => iteratedFDeriv ℝ m (f j) y v with hG
  have hGm : ∀ j, ContDiff ℝ m (f j) :=
    fun j => (hf j).of_le (by exact_mod_cast (Nat.le_trans hm (Nat.le_succ k)))
  have hG1 : ∀ j, ContDiff ℝ 1 (G j) := fun j => contDiff_one_iteratedFDeriv_apply hm (hf j) v
  have hGvan : ∀ j y, (∃ i, r i ≤ ‖y i - c i‖) → G j y = 0 := fun j y hy => by
    have h0 : iteratedFDeriv ℝ m (f j) y = 0 :=
      bmIter_vanishing hr (fun w hw => hsat j w hw) hy
    simp [hG, h0]
  have hxfull : x ∈ polydisc c r := polydisc_mono (fun j => by linarith [hr j]) hx
  have hyfull : y ∈ polydisc c r := polydisc_mono (fun j => by linarith [hr j]) hy
  have hsum : (∑ j, holderNorm 0 α (G j) Set.univ)
      ≤ ENNReal.ofReal (∏ i, ‖v i‖) * (∑ j, holderNorm k α (f j) Set.univ) := by
    calc ∑ j, holderNorm 0 α (G j) Set.univ
        ≤ ∑ j, ENNReal.ofReal (∏ i, ‖v i‖) * holderNorm k α (f j) Set.univ :=
          Finset.sum_le_sum fun j _ => bmIter_holderNorm_zero_le hm v
      _ = ENNReal.ofReal (∏ i, ‖v i‖) * ∑ j, holderNorm k α (f j) Set.univ := by
          rw [Finset.mul_sum]
  have hpos : 0 < ‖x - y‖ ^ α :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
  have hsem : ENNReal.ofReal (‖bmPotential G x - bmPotential G y‖ / ‖x - y‖ ^ α)
      ≤ ENNReal.ofReal C₀
          * (ENNReal.ofReal (∏ i, ‖v i‖) * ∑ j, holderNorm k α (f j) Set.univ) := by
    calc ENNReal.ofReal (‖bmPotential G x - bmPotential G y‖ / ‖x - y‖ ^ α)
        = ENNReal.ofReal (‖iteratedFDerivWithin ℝ 0 (bmPotential G) (polydisc c r) x
              - iteratedFDerivWithin ℝ 0 (bmPotential G) (polydisc c r) y‖ / ‖x - y‖ ^ α) := by
            rw [norm_iteratedFDerivWithin_zero_sub]
      _ ≤ holderSeminorm 0 α (bmPotential G) (polydisc c r) :=
            le_holderSeminorm 0 α _ _ hxfull hyfull hxy
      _ ≤ holderNorm 1 α (bmPotential G) (polydisc c r) :=
            holderSeminorm_le_holderNorm 1 α _ _ (Nat.zero_le 1)
      _ ≤ ENNReal.ofReal C₀ * ∑ j, holderNorm 0 α (G j) Set.univ := hC₀ G hG1 hGvan
      _ ≤ ENNReal.ofReal C₀
            * (ENNReal.ofReal (∏ i, ‖v i‖) * ∑ j, holderNorm k α (f j) Set.univ) := by gcongr
  have hclear : ENNReal.ofReal ‖bmPotential G x - bmPotential G y‖
      ≤ (ENNReal.ofReal C₀
            * (ENNReal.ofReal (∏ i, ‖v i‖) * ∑ j, holderNorm k α (f j) Set.univ))
          * ENNReal.ofReal (‖x - y‖ ^ α) := by
    have h := hsem
    rw [ENNReal.ofReal_div_of_pos hpos,
        ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top] at h
    exact h
  have hcommx := bmPotential_iteratedFDeriv hn hr hGm hsat v x
  have hcommy := bmPotential_iteratedFDeriv hn hr hGm hsat v y
  rw [hcommx, hcommy]
  change ENNReal.ofReal ‖bmPotential G x - bmPotential G y‖ ≤ _
  calc ENNReal.ofReal ‖bmPotential G x - bmPotential G y‖
      ≤ (ENNReal.ofReal C₀
            * (ENNReal.ofReal (∏ i, ‖v i‖) * ∑ j, holderNorm k α (f j) Set.univ))
          * ENNReal.ofReal (‖x - y‖ ^ α) := hclear
    _ = (ENNReal.ofReal C₀ * (∑ j, holderNorm k α (f j) Set.univ)
            * ENNReal.ofReal (‖x - y‖ ^ α)) * ENNReal.ofReal (∏ i, ‖v i‖) := by ac_rfl

/-! ## The theorem -/

/-- **Lower-order Schauder bounds for the iterated derivatives of the Bochner–Martinelli
potential**, given the order-zero estimate as a hypothesis.

Assume the order-zero (Calderón–Zygmund) estimate for the polydisc `polydisc c (2r)`: for every
`C¹` family `g` vanishing where `∃ i, r i ≤ ‖z i - c i‖`,
`‖bmPotential g‖_{C^{1,α}(polydisc c r)} ≤ C₀ Σ_j ‖g_j‖_{C^{0,α}}`.  Then for every `k` there is
`C` such that every family `f` with `C^{k+1}` components supported in `polydisc c (r/2)`
satisfies, for every `m ≤ k`,

`‖D^m (bmPotential f)‖_{sup on polydisc c (r/2)} ≤ C Σ_j ‖f_j‖_{C^{k,α}(ℂⁿ)}`

and the same bound with the sup replaced by the Hölder-`α` seminorm of `D^m`.  The proof is the
commutation identity `bmPotential_iteratedFDeriv`: the `m`-th iterated derivative of the
potential is the potential of the `m`-th iterated derivative of the data, which for `m ≤ k` is
again `C¹` and vanishes outside `polydisc c r`, so the hypothesis applies to it. -/
theorem bmPotential_iter_bound {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ}
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : ∀ j, 0 < r j) (k : ℕ)
    (hbase : ∃ C : ℝ, 0 < C ∧ ∀ g : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (g j)) →
      (∀ j z, (∃ i, r i ≤ ‖z i - c i‖) → g j z = 0) →
      holderNorm 1 α (bmPotential g) (polydisc c r)
        ≤ ENNReal.ofReal C * ∑ j, holderNorm 0 α (g j) Set.univ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ (k + 1) (f j)) →
      (∀ j z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → f j z = 0) →
      ∀ m, m ≤ k →
        (iterDerivNorm m (bmPotential f) (polydisc c (fun j => r j / 2))
            ≤ ENNReal.ofReal C * ∑ j, holderNorm k α (f j) Set.univ) ∧
        (holderSeminorm m α (bmPotential f) (polydisc c (fun j => r j / 2))
            ≤ ENNReal.ofReal C * ∑ j, holderNorm k α (f j) Set.univ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hbase
  refine ⟨C₀, hC₀pos, ?_⟩
  intro f hf hsat m hmk
  have hΩopen : IsOpen (polydisc c (fun j => r j / 2)) := isOpen_polydisc c _
  constructor
  · refine iSup₂_le fun z hz => ?_
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m hΩopen hz]
    refine ofReal_opNorm_le_of_bound_prod _ fun v => ?_
    exact bmPotential_iter_apply_le hn hr hmk hC₀ hf hsat v z hz
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
    rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m hΩopen hx,
        iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m hΩopen hy]
    have hpos : 0 < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    rw [ENNReal.ofReal_div_of_pos hpos,
        ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top]
    refine ofReal_opNorm_le_of_bound_prod _ fun v => ?_
    rw [sub_apply]
    exact bmPotential_iter_sub_le hn hr hmk hC₀ hf hsat v x y hx hy hxy

end Work.CR.Flat.Cauchy
