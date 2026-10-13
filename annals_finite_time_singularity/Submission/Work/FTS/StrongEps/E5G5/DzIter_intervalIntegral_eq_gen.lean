import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsSlotAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G5

/-- **The radial exchange, for an arbitrary order `n`.**

The boundedness hypothesis `hbdd` is only assumed for the slots `D_z^j D_θ^i` of order
`j + i ≤ n`; the conclusion is the exchange of the `k`-th radial operator `D_z^k` with the
interval integral in `s`, provided `k + l ≤ n` (so that every slot produced by the
induction is covered by `hbdd`).

The proof is the verbatim induction on `k` of `Work.FTS.StrongEps.DzIter_intervalIntegral_eq`
(the case `n = 4`), with `4` replaced by `n`: at the successor stage the new slot is
`D_z^{k+1} D_θ^l`, of order `(k+1) + l ≤ n`, and the induction hypothesis is applied at the
order `k + l ≤ n`. -/
theorem DzIter_intervalIntegral_eq_gen {H : ℝ → ℝ → ℝ → ℝ} {T a b C z₁ z₂ θ₁ θ₂ : ℝ} {n : ℕ}
    (haT : a ∈ Set.Icc 0 T) (hbT : b ∈ Set.Icc 0 T) (hab : a ≤ b) (hC : 0 ≤ C)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (H s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ n → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ → |Work.Spaces.mixed k l (H s) q.1 q.2| ≤ C)
    (hboxQ : Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ ⊆ Work.FTS.EllipticEst.Q0)
    (k l : ℕ) (hkl : k + l ≤ n) :
    ∀ z θ : ℝ, (z, θ) ∈ Set.Ioo z₁ z₂ ×ˢ Set.Ioo θ₁ θ₂ →
      Work.Spaces.DzIter k (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) z θ
        = ∫ s in a..b, Work.Spaces.DzIter k (Work.Spaces.DthIter l (H s)) z θ := by
  have hsub : Set.uIoc a b ⊆ Set.Icc (0:ℝ) T := by
    intro t ht
    rw [Set.uIoc_of_le hab] at ht
    exact ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  have hsubIoc : Set.Ioc a b ⊆ Set.Icc (0:ℝ) T := fun t ht =>
    ⟨le_trans haT.1 ht.1.le, le_trans ht.2 hbT.2⟩
  induction k with
  | zero => intro z θ _; rfl
  | succ k ih =>
    intro z θ hzθ
    rw [Set.mem_prod] at hzθ
    obtain ⟨hzz, hθθ⟩ := hzθ
    have hθcl : θ ∈ Set.Icc θ₁ θ₂ := ⟨le_of_lt hθθ.1, le_of_lt hθθ.2⟩
    have hzQ : (z, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      hboxQ ⟨⟨le_of_lt hzz.1, le_of_lt hzz.2⟩, hθcl⟩
    obtain ⟨hz0, hθ0, hθπ2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzQ
    set zlo : ℝ := max z₁ (z / 2) with hzlo
    have hzlo_lt : zlo < z := by
      rw [hzlo]; exact max_lt hzz.1 (by linarith)
    have hmem_box : ∀ x ∈ Set.Ioo zlo z₂,
        (x, θ) ∈ Set.Icc z₁ z₂ ×ˢ Set.Icc θ₁ θ₂ := by
      intro x hx
      exact ⟨⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx.1), le_of_lt hx.2⟩, hθcl⟩
    have hxQ : ∀ x ∈ Set.Ioo zlo z₂, (x, θ) ∈ Work.FTS.EllipticEst.Q0 :=
      fun x hx => hboxQ (hmem_box x hx)
    have hxpos : ∀ x ∈ Set.Ioo zlo z₂, 0 < x := fun x hx =>
      lt_of_lt_of_le (by linarith : (0:ℝ) < z / 2)
        (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx.1))
    have hcore := Work.FTS.StrongEps.hasDerivAt_intervalIntegral_of_deriv_le (a := a) (b := b)
      (G := fun t x => Work.Spaces.DzIter k (Work.Spaces.DthIter l (H t)) x θ)
      (G' := fun t x => Work.Spaces.mixed (k + 1) l (H t) x θ / x)
      (bound := fun _ => C * (2 / z)) hzlo_lt hzz.2 ?_ ?_ ?_ ?_ ?_ ?_
    rotate_left
    · intro x hx
      have := (hmeas k l x θ (hxQ x hx)).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [Work.Spaces.mixed] using this
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
      refine IntegrableOn.of_bound ?_ ?_ C ?_
      · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
      · have h1 := (hmeas k l z θ hzQ).mono_measure (Measure.restrict_mono hsubIoc le_rfl)
        simpa only [Work.Spaces.mixed] using h1
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        rw [Real.norm_eq_abs]
        have htT : t ∈ Set.Icc (0:ℝ) T := hsubIoc ht
        exact hbdd t htT k l (by omega) (z, θ) ⟨⟨le_of_lt hzz.1, le_of_lt hzz.2⟩, hθcl⟩
    · have h1 := (hmeas (k + 1) l z θ hzQ).mono_measure (Measure.restrict_mono hsub le_rfl)
      simpa only [div_eq_mul_inv] using h1.mul_const z⁻¹
    · intro t ht x hx
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hx2 : z / 2 ≤ x := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hx.1)
      have hb := hbdd t htT (k + 1) l (by omega) (x, θ) (hmem_box x hx)
      calc |Work.Spaces.mixed (k + 1) l (H t) x θ / x|
          = |Work.Spaces.mixed (k + 1) l (H t) x θ| / x := by
            rw [abs_div, abs_of_pos (hxpos x hx)]
        _ ≤ C / x := div_le_div_of_nonneg_right hb (le_of_lt (hxpos x hx))
        _ ≤ C / (z / 2) := div_le_div_of_nonneg_left hC (by linarith) hx2
        _ = C * (2 / z) := by field_simp
    · exact intervalIntegrable_const
    · intro t ht x hx
      have htT : t ∈ Set.Icc (0:ℝ) T := hsub ht
      have hder : HasDerivAt (fun x' => Work.Spaces.mixed k l (H t) x' θ)
          (Work.Spaces.pz (Work.Spaces.mixed k l (H t)) x θ) x :=
        Work.FTS.EllipticEst.SmoothOpen.hasDerivAt_slice
          (Work.FTS.LocData.contDiffOn_mixed Work.FTS.EllipticEst.isOpen_Q0 (hsm t htT) k l)
          (θ := θ) ⟨hθ0, hθπ2⟩ (hxpos x hx)
      exact hder.congr_deriv
        (Work.FTS.StrongEps.LocUnif.pz_mixed_div k l (hsm t htT) x θ (hxQ x hx))
    have hloc : (fun x => Work.Spaces.DzIter k
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) x θ)
        =ᶠ[𝓝 z] (fun x => ∫ s in a..b, Work.Spaces.DzIter k (Work.Spaces.DthIter l (H s)) x θ) := by
      filter_upwards [isOpen_Ioo.mem_nhds hzz] with x hx
      exact ih (by omega) x θ ⟨hx, hθθ⟩
    have hpz : Work.Spaces.pz (Work.Spaces.DzIter k
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ)) z θ
        = ∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ / z := by
      show deriv (fun x => Work.Spaces.DzIter k
        (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) x θ) z = _
      rw [hloc.deriv_eq, hcore.deriv]
    have hzne : z ≠ 0 := ne_of_gt hz0
    calc Work.Spaces.DzIter (k + 1)
          (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ) z θ
        = z * Work.Spaces.pz (Work.Spaces.DzIter k
            (fun z θ => ∫ s in a..b, Work.Spaces.DthIter l (H s) z θ)) z θ := by
          rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
      _ = z * (∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ / z) := by rw [hpz]
      _ = z * ((∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ) / z) := by
          rw [intervalIntegral.integral_div]
      _ = ∫ s in a..b, Work.Spaces.mixed (k + 1) l (H s) z θ := mul_div_cancel₀ _ hzne
      _ = ∫ s in a..b, Work.Spaces.DzIter (k + 1) (Work.Spaces.DthIter l (H s)) z θ := rfl

end Work.FTS.StrongEps.E5G5
