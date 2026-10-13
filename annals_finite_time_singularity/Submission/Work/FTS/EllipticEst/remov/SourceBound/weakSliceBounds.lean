import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.H2W.Fstar_DzIter_le_Psi
import Submission.Work.FTS.EllipticEst.remov.weakSliceRegular
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Helper lemmas

The proof of the target consists in applying the one-dimensional boundedness lemma
`Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta` (boundedness of a slice and of its
`θ`-derivative from the weighted `L²`-integrability of the slice's second derivative) to the two
slices `θ ↦ Ψ z θ` and `θ ↦ ∂_zΨ(z,θ)`, whose second `θ`-derivatives are the slots
`∂_θθΨ` resp. `∂_z∂_θθΨ` of the `ℋ^k`-membership hypotheses (`k ≥ 2`).  The only structural
input is the Clairaut identity `∂_θθ ∂_zΨ = ∂_z ∂_θθΨ` on the open quadrant. -/

/-- `SmoothOpen` is closed under the `∂_θ`-iterates. -/
theorem smoothOpen_pthIter {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (i : ℕ) : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter i f) := by
  induction i with
  | zero => simpa using hf
  | succ i ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

/-- **Clairaut at order `3` for the slices of a `C^∞` function on the open quadrant**:
`∂_θθ (∂_z f) = ∂_z (∂_θθ f)` on `Q0`.

This is two applications of the Clairaut identity `Work.Spaces.pz_pth_comm`
(one for `f`, one for `Work.Spaces.pth f`), transported across the `θ`-derivative by the
locality of `deriv` on the open interval. -/
theorem pthIter2_pz_eqOn {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter 2 (Work.Spaces.pz f)))
      (Function.uncurry (Work.Spaces.pz (Work.Spaces.pthIter 2 f)))
      Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ hp
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have hθIoo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- `∂_θ (∂_θ ∂_z f) = ∂_θ (∂_z ∂_θ f)` at `(z,θ)`
  have hstep1 : Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.pz f)) z θ
      = Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth f)) z θ := by
    have hev : (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.pz f) z θ')
        =ᶠ[𝓝 θ] (fun θ' : ℝ => Work.Spaces.pz (Work.Spaces.pth f) z θ') := by
      filter_upwards [isOpen_Ioo.mem_nhds hθIoo] with θ' hθ'
      exact (Work.Spaces.pz_pth_comm (f := f)
        ((hf.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩))).of_le (by simp))).symm
    show deriv (fun θ' : ℝ => Work.Spaces.pth (Work.Spaces.pz f) z θ') θ
        = deriv (fun θ' : ℝ => Work.Spaces.pz (Work.Spaces.pth f) z θ') θ
    rw [hev.deriv_eq]
  -- `∂_θ (∂_z ∂_θ f) = ∂_z (∂_θ ∂_θ f)` at `(z,θ)`: this is Clairaut for `∂_θ f`
  have hstep2 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pth f)) z θ
      = Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth f)) z θ :=
    (Work.Spaces.pz_pth_comm (f := Work.Spaces.pth f)
      (((smoothOpen_pthIter hf 1).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
        (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩))).of_le (by simp))).symm
  show Work.Spaces.pthIter 2 (Work.Spaces.pz f) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter 2 f) z θ
  simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]
  rw [hstep1, hstep2]

/-- **Boundedness of a slice and of its derivative from the weighted `L²`-bound on the second
derivative.**  If `u` is `C²` on the open interval, the second `θ`-derivative of `u` agrees there
with `v`, and `v²·sEta` is integrable on `Iθ`, then `u` and `u'` are bounded on the open
interval.  (The route is the one of `abs_le_of_sq_mul_sEta`: `v²·sEta` integrable forces
`v ∈ L¹` because `sEta ≥ 1`, and an oscillation bound plus one more integration bounds `u'` and
`u`.) -/
theorem exists_bdd_of_sq_mul_sEta {u v : ℝ → ℝ}
    (hsm : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), deriv (deriv u) θ = v θ)
    (hint : MeasureTheory.IntegrableOn
      (fun θ => (v θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u θ| ≤ C ∧ |u θ| ≤ C := by
  have hae : (fun θ => (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ => (v θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => ?_)
    show (deriv (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (v θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [hv θ hθ]
  exact Work.FTS.EllipticEst.remov.abs_le_of_sq_mul_sEta hsm (hint.congr hae.symm)

/-- The eight endpoint values, at the two ends of the angular interval, of the four functions
occurring in `weakSliceBounds` (the slice `Ψ(z,·)` and its three partials).  Nothing is assumed
about `Ψ` for `θ < 0`, so these are simply real numbers to be absorbed into the constant `M`;
their finite sum is what enters `M`. -/
noncomputable def endVals (z : ℝ) (Ψ : ℝ → ℝ → ℝ) : Finset ℝ :=
  {|Ψ z 0|, |Work.Spaces.pth Ψ z 0|, |Work.Spaces.pz Ψ z 0|,
    |Work.Spaces.pz (Work.Spaces.pth Ψ) z 0|, |Ψ z (Real.pi / 2)|,
    |Work.Spaces.pth Ψ z (Real.pi / 2)|, |Work.Spaces.pz Ψ z (Real.pi / 2)|,
    |Work.Spaces.pz (Work.Spaces.pth Ψ) z (Real.pi / 2)|}

/-- **Pointwise bounds on the angular slices of a weak datum.**

For every `z > 0` the four functions `θ ↦ Ψ(z,θ)`, `θ ↦ ∂_θΨ(z,θ)`, `θ ↦ ∂_zΨ(z,θ)` and
`θ ↦ ∂_z∂_θΨ(z,θ)` are bounded on the angular interval `Iθ = [0,π/2]`.

The bounds on the open interval are those of `exists_bdd_of_sq_mul_sEta`, applied to the two
slices `u = Ψ(z,·)` and `u = ∂_zΨ(z,·)`: their second `θ`-derivatives are the slots
`∂_θθΨ` and `∂_z∂_θθΨ` of `Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ)` (available because
`k ≥ 2`), and `∂_θθ∂_zΨ = ∂_z∂_θθΨ` is Clairaut (`pthIter2_pz_eqOn`).  At the two endpoints the
values are those of an arbitrary function `Ψ : ℝ → ℝ → ℝ` (nothing is assumed for `θ < 0`), so
they are simply absorbed into the constant `M`. -/
theorem weakSliceBounds {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ z, 0 < z → ∃ M : ℝ, 0 ≤ M ∧ ∀ θ ∈ Work.Spaces.Iθ,
      |Ψ z θ| ≤ M ∧
      |Work.Spaces.pth Ψ z θ| ≤ M ∧
      |Work.Spaces.pz Ψ z θ| ≤ M ∧
      |Work.Spaces.pz (Work.Spaces.pth Ψ) z θ| ≤ M := by
  intro z hz
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hB : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 Ψ) :=
    smoothOpen_pthIter hS 2
  -- ## The two `ℋ^k`-slots as honest `L²(sEta)` statements on the slice `z`
  have hI0 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    simpa [Work.FTS.EllipticEst.sEta]
      using Work.FTS.EllipticEst.H2W.slot_slice_integrableOn hB h.memB 0 (by omega) hz
  have hI2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    have h1 := Work.FTS.EllipticEst.H2W.slot_slice_integrableOn hB h.memB 1 (by omega) hz
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))) Work.Spaces.Iθ := h1.const_mul _
    refine h2.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    show (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      = (Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz,
      Work.FTS.EllipticEst.sEta]
    field_simp
  -- ## The two slices and their second `θ`-derivatives
  have hu1 : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hS.curry_θ hz).of_le (by simp)
  have hu2 : ContDiffOn ℝ 2 (fun θ : ℝ => Work.Spaces.pz Ψ z θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (hS.pz.curry_θ hz).of_le (by simp)
  have hv1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (deriv (fun θ' : ℝ => Ψ z θ')) θ = Work.Spaces.pthIter 2 Ψ z θ := by
    intro θ hθ
    show Work.Spaces.pthIter 2 Ψ z θ = Work.Spaces.pthIter 2 Ψ z θ
    rfl
  have hv2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv (deriv (fun θ' : ℝ => Work.Spaces.pz Ψ z θ')) θ
        = Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ := by
    intro θ hθ
    show Work.Spaces.pthIter 2 (Work.Spaces.pz Ψ) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter 2 Ψ) z θ
    exact pthIter2_pz_eqOn hS (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
  obtain ⟨C1, hC1pos, hC1⟩ := exists_bdd_of_sq_mul_sEta hu1 hv1 hI0
  obtain ⟨C2, hC2pos, hC2⟩ := exists_bdd_of_sq_mul_sEta hu2 hv2 hI2
  -- ## Assembly: the interior constant plus the eight endpoint values
  have hA0 : 0 ≤ max C1 C2 := hC1pos.le.trans (le_max_left _ _)
  have hVnn : ∀ y ∈ endVals z Ψ, 0 ≤ y := by
    intro y hy
    simp only [endVals, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h | h | h | h | h | h <;> · rw [h]; positivity
  have hT0 : 0 ≤ (endVals z Ψ).sum id := Finset.sum_nonneg hVnn
  refine ⟨max C1 C2 + (endVals z Ψ).sum id, add_nonneg hA0 hT0, ?_⟩
  intro θ hθ
  have hmid : max C1 C2 ≤ max C1 C2 + (endVals z Ψ).sum id := le_add_of_nonneg_right hT0
  have hEnd : ∀ x ∈ endVals z Ψ, x ≤ max C1 C2 + (endVals z Ψ).sum id := by
    intro x hx
    exact (Finset.single_le_sum hVnn hx).trans (le_add_of_nonneg_left hA0)
  rcases eq_or_lt_of_le hθ.1 with h0 | h0lt
  · subst h0
    exact ⟨hEnd _ (by simp [endVals]), hEnd _ (by simp [endVals]),
      hEnd _ (by simp [endVals]), hEnd _ (by simp [endVals])⟩
  · rcases eq_or_lt_of_le hθ.2 with hpi | hpit
    · subst hpi
      exact ⟨hEnd _ (by simp [endVals]), hEnd _ (by simp [endVals]),
        hEnd _ (by simp [endVals]), hEnd _ (by simp [endVals])⟩
    · -- interior point: use the two boundedness statements
      have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h0lt, hpit⟩
      have hb1 := hC1 θ hθ'
      have hb2 := hC2 θ hθ'
      have hcomm : deriv (fun θ' : ℝ => Work.Spaces.pz Ψ z θ') θ
          = Work.Spaces.pz (Work.Spaces.pth Ψ) z θ := by
        show Work.Spaces.pth (Work.Spaces.pz Ψ) z θ
          = Work.Spaces.pz (Work.Spaces.pth Ψ) z θ
        exact (Work.Spaces.pz_pth_comm (f := Ψ)
          ((hS.contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
            (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ'.1, hθ'.2⟩))).of_le (by simp))).symm
      exact ⟨(hb1.2.trans (le_max_left C1 C2)).trans hmid,
        (hb1.1.trans (le_max_left C1 C2)).trans hmid,
        (hb2.2.trans (le_max_right C1 C2)).trans hmid,
        ((hcomm ▸ hb2.1).trans (le_max_right C1 C2)).trans hmid⟩

end Work.FTS.EllipticEst.remov.SourceBound
