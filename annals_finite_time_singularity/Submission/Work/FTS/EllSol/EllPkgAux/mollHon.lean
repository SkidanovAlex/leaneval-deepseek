import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.thMoll_hasDerivAt
import Submission.Work.FTS.EllSol.EllPkgAux.MollDzAux.qext_continuousOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

/-!
# `mollHon` — a.e. strong measurability of the approximant's slice integrand

`mollHon` is the measurability half of the Fatou step of the mollification transfer
(`mollFatou`): the slice integrand

`θ ↦ (D_z∂_θ Φ(z,θ))² σ_η(θ)`,   `Φ = zmoll G t t`,

is a.e. strongly measurable on `Iθ`, *given* the identity `hid` that rewrites `D_z∂_θΦ` as the
double convolution of the datum `G` against the derivative kernels `sKerd t`.

The point of the lemmas below is that the datum `G` is only assumed `C^∞` on the **open**
quadrant `Q0` (`SmoothOpen G`): its values on the angular boundary lines `θ = 0, π/2` and
outside the closed quadrant are junk and need never enter.  We therefore

* replace `G` by its trivial extension `Kq G` off `Q0` (measurable, by
  `ContinuousOn.measurable_piecewise`), and
* replace the doubly-odd extension `Qext G (exp t') ·` of `Hxyc` by the branch function `Hm G`,
  which is *globally* measurable and agrees with `Qext G (exp t') ·` wherever the kernel
  `sKerd t (θ - ·)` is non-zero, for `θ ∈ Iθ` and `t ≤ 1/2` (up to the null set `{0, π/2}`).

Then two applications of Fubini's measurability theorem
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`) give the a.e. strong measurability
of the double convolution, and `hid` transfers it to the slice integrand.
-/

/-- The trivial extension of the datum to the whole plane: the datum on the open quadrant, zero
elsewhere.  Its only role is to make the angular integrand of the two convolutions *globally*
measurable. -/
def Kq (G : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => if 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2 then G p.1 p.2 else 0

theorem measurable_Kq (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G) :
    Measurable (Kq G) := by
  classical
  have h := ContinuousOn.measurable_piecewise (f := Function.uncurry G)
    (g := fun _ : ℝ × ℝ => (0 : ℝ)) hS.continuousOn continuousOn_const
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  convert h using 1
  funext p
  unfold Kq Set.piecewise Function.uncurry
  by_cases hp : 0 < p.1 ∧ 0 < p.2 ∧ p.2 < Real.pi / 2
  · rw [if_pos hp, if_pos (Work.FTS.EllipticEst.mem_Q0.mpr hp)]
  · rw [if_neg hp, if_neg (fun hh => hp (Work.FTS.EllipticEst.mem_Q0.mp hh))]

/-- The branch function replacing the doubly-odd extension `Qext G (exp t') s` in the angular
convolution: on `s < 0` it is the reflected branch `-G (exp t') (-s)`, on `0 ≤ s ≤ π/2` the
datum itself and on `s > π/2` the second reflected branch `-G (exp t') (π - s)`, each read
through the trivial extension `Kq G` of the datum. -/
def Hm (G : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p =>
    if p.2 < 0 then -Kq G (Real.exp p.1, -p.2)
    else if p.2 ≤ Real.pi / 2 then Kq G (Real.exp p.1, p.2)
    else -Kq G (Real.exp p.1, Real.pi - p.2)

theorem measurable_Hm (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G) :
    Measurable (Hm G) := by
  have hK : Measurable (Kq G) := measurable_Kq G hS
  have hA : Measurable (fun p : ℝ × ℝ => -Kq G (Real.exp p.1, -p.2)) :=
    Measurable.neg (hK.comp ((Real.continuous_exp.comp continuous_fst).prodMk
      continuous_snd.neg).measurable)
  have hB : Measurable (fun p : ℝ × ℝ => Kq G (Real.exp p.1, p.2)) :=
    hK.comp ((Real.continuous_exp.comp continuous_fst).prodMk continuous_snd).measurable
  have hC : Measurable (fun p : ℝ × ℝ => -Kq G (Real.exp p.1, Real.pi - p.2)) :=
    Measurable.neg (hK.comp ((Real.continuous_exp.comp continuous_fst).prodMk
      (continuous_const.sub continuous_snd)).measurable)
  have hinner : Measurable (fun p : ℝ × ℝ =>
      if p.2 ≤ Real.pi / 2 then Kq G (Real.exp p.1, p.2)
      else -Kq G (Real.exp p.1, Real.pi - p.2)) :=
    Measurable.ite (measurableSet_le measurable_snd measurable_const) hB hC
  have houter : Measurable (fun p : ℝ × ℝ =>
      if p.2 < 0 then -Kq G (Real.exp p.1, -p.2)
      else if p.2 ≤ Real.pi / 2 then Kq G (Real.exp p.1, p.2)
      else -Kq G (Real.exp p.1, Real.pi - p.2)) :=
    Measurable.ite (measurableSet_lt measurable_snd measurable_const) hA hinner
  unfold Hm
  exact houter

/-- **The angular integrands of `Hxyc` and of `Hm` have the same convolution integral.**
For `θ ∈ Iθ` and any `t'`, the two `s`-integrands agree except on the null set `{0, π/2}`:
off the kernel window `|θ - s| ≤ t` the factor `sKerd t (θ - s)` vanishes, and inside it every
argument at which `Kq G` is evaluated lies in the open quadrant, where `Kq G` is the datum and
the branches of `Qext` reproduce the three cases of `Hm G`. -/
theorem sKerd_mul_Hxyc_eq_Hm (G : ℝ → ℝ → ℝ)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (t' : ℝ) :
    ∫ s : ℝ, sKerd t (θ - s) * Hxyc G t' s
      = ∫ s : ℝ, sKerd t (θ - s) * Hm G (t', s) := by
  have key : ∀ s : ℝ, s ≠ 0 → s ≠ Real.pi / 2 →
      sKerd t (θ - s) * Hxyc G t' s = sKerd t (θ - s) * Hm G (t', s) := by
    intro s hs0 hspi
    by_cases hk : sKerd t (θ - s) = 0
    · rw [hk, zero_mul, zero_mul]
    · have hwin : |θ - s| ≤ t := by
        by_contra hlt
        exact hk (MollDzAux.sKerd_eq_zero_of_lt_abs ht0 (lt_of_not_ge hlt))
      have hb : -t ≤ θ - s ∧ θ - s ≤ t := abs_le.mp hwin
      obtain ⟨hθ0, hθ1⟩ := Set.mem_Icc.mp hθ
      have hpt : Hxyc G t' s = Hm G (t', s) := by
        rcases lt_trichotomy s 0 with hs | hs | hs
        · have hmem : 0 < -s ∧ -s < Real.pi / 2 :=
            ⟨by linarith, by linarith [hb.2, ht1, Real.pi_gt_three]⟩
          have hKq : Kq G (Real.exp t', -s) = G (Real.exp t') (-s) := by
            unfold Kq
            rw [if_pos ⟨Real.exp_pos t', hmem.1, hmem.2⟩]
          unfold Hxyc Hm
          rw [if_pos hs, MollDzAux.Qext_of_lt_zero G (Real.exp t') s hs, hKq]
        · exact absurd hs hs0
        · by_cases hsle : s ≤ Real.pi / 2
          · have hmem : 0 < s ∧ s < Real.pi / 2 := ⟨hs, lt_of_le_of_ne hsle hspi⟩
            have hKq : Kq G (Real.exp t', s) = G (Real.exp t') s := by
              unfold Kq
              rw [if_pos ⟨Real.exp_pos t', hmem.1, hmem.2⟩]
            unfold Hxyc Hm
            rw [if_neg (not_lt.mpr (le_of_lt hs)), if_pos hsle,
              Work.FTS.EllSol.PkgK5.K5c.Qext_of_mem G (Real.exp t') s ⟨le_of_lt hs, hsle⟩,
              hKq]
          · have hmem : 0 < Real.pi - s ∧ Real.pi - s < Real.pi / 2 :=
              ⟨by linarith [hb.1, hθ1, ht1, Real.pi_gt_three], by linarith⟩
            have hKq : Kq G (Real.exp t', Real.pi - s) = G (Real.exp t') (Real.pi - s) := by
              unfold Kq
              rw [if_pos ⟨Real.exp_pos t', hmem.1, hmem.2⟩]
            unfold Hxyc Hm
            rw [if_neg (not_lt.mpr (le_of_lt hs)), if_neg hsle,
              MollDzAux.Qext_of_pihalf_lt G (Real.exp t') s (not_le.mp hsle), hKq]
      rw [hpt]
  refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_iff.mpr ?_)
  refine measure_mono_null ?_ (Set.Finite.measure_zero
    ((Set.finite_singleton (Real.pi / 2)).insert 0) volume)
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_contra hcon
  push_neg at hcon
  exact hs (key s hcon.1 hcon.2)

theorem mollHon (G : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen G) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 2) (z : ℝ) (hz : 0 < z) (hid : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G t t)) z θ = ∫ t' : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t (Real.log z - t') * (∫ s : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd t (θ - s) * Work.FTS.EllSol.EllPkgAux.Hxyc G t' s)) : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G t t)) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  set μθ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict Work.Spaces.Iθ with hμθ
  -- the angular weight `σ_η` is a.e. strongly measurable on `Iθ`
  have hth : MeasureTheory.AEStronglyMeasurable Work.FTS.EllipticEst.thEta μθ := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
    have hne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := by
      intro θ hθ
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos]))
    have hcont : ContinuousOn Work.FTS.EllipticEst.thEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      change ContinuousOn (fun θ : ℝ => Real.sin (2 * θ) ^ (-(Work.Spaces.eta)))
        (Set.Ioo (0 : ℝ) (Real.pi / 2))
      exact hsin.rpow_const (fun θ hθ => Or.inl (hne θ hθ))
    have hrest : MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) = μθ := by
      rw [hμθ]
      exact Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc
        (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ)) (a := 0) (b := Real.pi / 2))
    rw [← hrest]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  -- the whole triple integrand is globally measurable
  have hf : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      sKerd t (Real.log z - p.1.2) * (sKerd t (p.1.1 - p.2) * Hm G (p.1.2, p.2))) := by
    have h1 : Measurable (fun p : (ℝ × ℝ) × ℝ => sKerd t (Real.log z - p.1.2)) :=
      (MollDzAux.continuous_sKerd t).measurable.comp
        (continuous_const.sub (continuous_snd.comp continuous_fst)).measurable
    have h2 : Measurable (fun p : (ℝ × ℝ) × ℝ => sKerd t (p.1.1 - p.2)) :=
      (MollDzAux.continuous_sKerd t).measurable.comp
        ((continuous_fst.comp continuous_fst).sub continuous_snd).measurable
    have h3 : Measurable (fun p : (ℝ × ℝ) × ℝ => Hm G (p.1.2, p.2)) :=
      (measurable_Hm G hS).comp ((continuous_snd.comp continuous_fst).prodMk
        continuous_snd).measurable
    exact h1.mul (h2.mul h3)
  -- Fubini, twice
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × ℝ => ∫ s : ℝ,
        sKerd t (Real.log z - q.2) * (sKerd t (q.1 - s) * Hm G (q.2, s)))
      (μθ.prod MeasureTheory.volume) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := μθ.prod MeasureTheory.volume) (ν := MeasureTheory.volume)
      (hf.aestronglyMeasurable)
  have h2 : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => ∫ t' : ℝ, ∫ s : ℝ,
        sKerd t (Real.log z - t') * (sKerd t (θ - s) * Hm G (t', s))) μθ :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := μθ) (ν := MeasureTheory.volume) h1
  -- pull the radial kernel factor out of the inner integral
  have hfix : (fun θ : ℝ => ∫ t' : ℝ, ∫ s : ℝ,
        sKerd t (Real.log z - t') * (sKerd t (θ - s) * Hm G (t', s)))
      = fun θ : ℝ => ∫ t' : ℝ, sKerd t (Real.log z - t')
          * (∫ s : ℝ, sKerd t (θ - s) * Hm G (t', s)) := by
    funext θ
    simp only [MeasureTheory.integral_const_mul]
  have h2r : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => ∫ t' : ℝ, sKerd t (Real.log z - t')
        * (∫ s : ℝ, sKerd t (θ - s) * Hm G (t', s))) μθ := hfix ▸ h2
  have hsq : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (∫ t' : ℝ, sKerd t (Real.log z - t')
        * (∫ s : ℝ, sKerd t (θ - s) * Hm G (t', s))) ^ 2
        * Work.FTS.EllipticEst.thEta θ) μθ :=
    (h2r.pow 2).mul hth
  -- transfer along `hid`, using the identity of the two angular integrands
  have hfun : (fun θ : ℝ => (∫ t' : ℝ, sKerd t (Real.log z - t')
        * (∫ s : ℝ, sKerd t (θ - s) * Hm G (t', s))) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      =ᵐ[μθ] (fun θ : ℝ =>
        (Work.Spaces.Dz (Work.Spaces.pth (Work.FTS.EllSol.PkgK5.K5c.zmoll G t t)) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) := by
    filter_upwards [MeasureTheory.ae_restrict_mem
      (show MeasurableSet Work.Spaces.Iθ from measurableSet_Icc)] with θ hθ
    have hint : (∫ t' : ℝ, sKerd t (Real.log z - t')
          * (∫ s : ℝ, sKerd t (θ - s) * Hm G (t', s)))
        = ∫ t' : ℝ, sKerd t (Real.log z - t')
          * (∫ s : ℝ, sKerd t (θ - s) * Hxyc G t' s) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t' => ?_)
      change sKerd t (Real.log z - t') * (∫ s : ℝ, sKerd t (θ - s) * Hm G (t', s))
        = sKerd t (Real.log z - t') * (∫ s : ℝ, sKerd t (θ - s) * Hxyc G t' s)
      rw [← sKerd_mul_Hxyc_eq_Hm G ht0 ht1 hθ t']
    rw [hint, hid θ hθ]
  exact hμθ ▸ hsq.congr hfun

end Work.FTS.EllSol.EllPkgAux

-- end of file
