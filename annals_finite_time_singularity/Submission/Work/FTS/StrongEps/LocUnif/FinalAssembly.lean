/-
Copyright: work module for the Elgindi finite-time singularity project.

# The final energy bound `HkNorm α 6 f ≤ B`

This module assembles the pieces that bound `HkSq α 6 f = ∫_z∈Iz ∫_θ∈Iθ HkIntegrand α 6 f z θ`
by `B ^ 2` for the limit `f` of a locally uniformly convergent subsequence `G (Φ n)` with
`HkNorm α 6 (G n) ≤ B`.

The strategy (see `NOTES_assembly_final.md`):

* On a box `[a,b] × [c,d] ⊆ (0,∞) × (0,π/2)` the slots of order `≤ 5` are handled by Fatou,
  the seven slots of order `6` through the measurable majorants `V6z`, `V6t` built from
  backward difference quotients of the level-5 slots;
* the resulting box bound is then exhausted (`setLIntegral_iUnion_of_directed`, the boundary of
  the box being null) to the whole open quadrant;
* finally the iterated lintegral is compared with the iterated Bochner integral defining `HkSq`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.LocUnif.V5Defs
import Submission.Work.FTS.StrongEps.LocUnif.V6Defs
import Submission.Work.FTS.StrongEps.LocUnif.lintegral_backwardDiffQuot_majorant_le_liminf_z
import Submission.Work.FTS.StrongEps.LocUnif.lintegral_backwardDiffQuot_majorant_le_liminf_theta
import Submission.Work.FTS.StrongEps.LocUnif.ofReal_HkIntegrand_six_le
import Submission.Work.FTS.StrongEps.LocUnif.level6_identities
import Submission.Work.FTS.StrongEps.LocUnif.lintegral_V5_le_liminf
import Submission.Work.FTS.StrongEps.LocUnif.V5_eq_ae
import Submission.Work.FTS.StrongEps.LocUnif.aemeasurable_ofReal_HkIntegrand
import Submission.Work.FTS.StrongEps.LocUnif.aemeasurable_V6
import Submission.Work.FTS.StrongEps.LocUnif.lintegral_subbox_eq_iSup
import Submission.Work.FTS.StrongEps.LocUnif.iUnion_subbox
import Submission.Work.FTS.StrongEps.LocUnif.volume_box_sdiff_openBox
import Submission.Work.FTS.CoercivityFix.Transfer.E2pkg.FinCalc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology Real

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false

/-- The open quadrant `(0,∞) × (0,π/2)` on which the whole argument takes place. -/
def Q0 : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem isOpen_Q0 : IsOpen Q0 := isOpen_Ioi.prod isOpen_Ioo

theorem box_subset_Q0 {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < π / 2) :
    Set.Icc a b ×ˢ Set.Icc c d ⊆ Q0 := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  exact ⟨lt_of_lt_of_le ha hz.1, lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩

/-- `C^k`-regularity on `Q0` gives continuity of every mixed block on `Q0`. -/
theorem continuousOn_mixed_Q0 {g : ℝ → ℝ → ℝ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry g) Q0) (j i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i g p.1 p.2) Q0 :=
  (Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le isOpen_Q0 i j 0
    (by omega) (hsm (j + i))).continuousOn

/-- The level-5 slots of the limit `f` are a.e. measurable on `Q0`, being a.e. limits of
continuous functions. -/
theorem aemeasurable_mixed_five {f : ℝ → ℝ → ℝ} {F : ℕ → ℝ → ℝ → ℝ}
    (hcont : ∀ n (j i : ℕ),
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i (F n) p.1 p.2) Q0)
    (hconv5 : ∀ᵐ p ∂(MeasureTheory.volume.restrict Q0), ∀ (j i : ℕ), j + i = 5 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (F n) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2)))
    {j i : ℕ} (hji : j + i = 5) :
    AEMeasurable (fun p : ℝ × ℝ => Work.Spaces.mixed j i f p.1 p.2)
      (MeasureTheory.volume.restrict Q0) := by
  have hmeas : ∀ n, AEMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.mixed j i (F n) p.1 p.2)
      (MeasureTheory.volume.restrict Q0) :=
    fun n => (hcont n j i).aemeasurable isOpen_Q0.measurableSet
  have hlim : AEMeasurable
      (fun p : ℝ × ℝ => Filter.liminf (fun n => Work.Spaces.mixed j i (F n) p.1 p.2)
        Filter.atTop) (MeasureTheory.volume.restrict Q0) :=
    AEMeasurable.liminf hmeas
  refine hlim.congr ?_
  filter_upwards [hconv5] with p hp
  exact (hp j i hji).liminf_eq

/-- The a.e. convergence on `Q0` restricts to any box inside `Q0`. -/
theorem ae_restrict_box {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < π / 2)
    {P : ℝ × ℝ → Prop}
    (h : ∀ᵐ p ∂(MeasureTheory.volume.restrict Q0), P p) :
    ∀ᵐ p ∂(MeasureTheory.volume.restrict (Set.Icc a b ×ˢ Set.Icc c d)), P p :=
  h.filter_mono (MeasureTheory.ae_mono
    (MeasureTheory.Measure.restrict_mono (box_subset_Q0 ha hc hd) (le_refl _)))

/-- `V6z` rewritten with a `Fin 6`-sum, so that the group majorant lemma (which is stated for a
finite type of slots) applies. -/
theorem V6z_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    V6z α f p = Filter.liminf (fun j : ℕ => ∑ i : Fin 6, ENNReal.ofReal
      (((Work.Spaces.mixed (5 - (i : ℕ)) (i : ℕ) f p.1 p.2
          - Work.Spaces.mixed (5 - (i : ℕ)) (i : ℕ) f
              (p.1 - 1 / ((j : ℝ) + 1)) p.2) * ((j : ℝ) + 1)
        * (p.1 * rho6 α (i : ℕ) p.1 p.2)) ^ 2)) Filter.atTop := by
  unfold V6z
  congr 1 with j

/-- `V6t` rewritten with the `θ`-difference quotient. -/
theorem V6t_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    V6t α f p = Filter.liminf (fun j : ℕ => ENNReal.ofReal
      (((Work.Spaces.mixed 0 5 f p.1 p.2
          - Work.Spaces.mixed 0 5 f p.1 (p.2 - 1 / ((j : ℝ) + 1))) * ((j : ℝ) + 1)
        * (Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)) ^ 2)) Filter.atTop := by
  rw [V6t]

/-! ## The level-5 slots and the weights, as named functions

These names make the instantiations of the majorant lemmas below readable. -/

/-- The level-5 slot `D_z^{5-k} D_θ^k` of a sequence member. -/
def Vslot (F : ℕ → ℝ → ℝ → ℝ) (n k : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.mixed (5 - k) k (F n) z θ

/-- The level-5 slot `D_z^{5-k} D_θ^k` of the limit. -/
def Wslot (f : ℝ → ℝ → ℝ) (k : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.mixed (5 - k) k f z θ

/-- The weight `z · rho6 α k` multiplying the `z`-difference quotient of the `k`-th level-5
slot. -/
def rhoZ (α : ℝ) (k : ℕ) : ℝ → ℝ → ℝ := fun z θ => z * rho6 α k z θ

/-- The weight `sin(2θ) · Wt α` multiplying the `θ`-difference quotient of `D_θ^5 f`. -/
def rhoT (α : ℝ) : ℝ → ℝ → ℝ := fun z θ => Real.sin (2 * θ) * rho6 α 6 z θ

/-- `V6z` in terms of the named level-5 slots. -/
theorem V6z_eq' (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    V6z α f p = Filter.liminf (fun j : ℕ => ∑ k : Fin 6, ENNReal.ofReal
      (((Wslot f (k : ℕ) p.1 p.2 - Wslot f (k : ℕ) (p.1 - 1 / ((j : ℝ) + 1)) p.2)
          * ((j : ℝ) + 1) * rhoZ α (k : ℕ) p.1 p.2) ^ 2)) Filter.atTop := by
  rw [V6z_eq]
  simp only [Wslot, rhoZ]

/-- `V6t` in terms of the named level-5 slot. -/
theorem V6t_eq' (α : ℝ) (f : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    V6t α f p = Filter.liminf (fun j : ℕ => ENNReal.ofReal
      (((Wslot f 5 p.1 p.2 - Wslot f 5 p.1 (p.2 - 1 / ((j : ℝ) + 1)))
          * ((j : ℝ) + 1) * rhoT α p.1 p.2) ^ 2)) Filter.atTop := by
  rw [V6t_eq]
  simp only [Wslot, rhoT]

/-! ## Continuity of the weights on a box -/

theorem continuousOn_w_box {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Icc a b) := by
  have h : ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Icc a b) :=
    ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
      (fun z hz => pow_ne_zero 2 (by linarith [hz.1]))
  simpa only [Work.Spaces.w] using h

theorem continuousOn_sin_rpow_box {c d p : ℝ} (hc : 0 < c) (hd : d < π / 2) :
    ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) (Set.Icc c d) := by
  have hpos : ∀ θ ∈ Set.Icc c d, 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hsin : Continuous (fun θ : ℝ => Real.sin (2 * θ)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  exact (hsin.continuousOn).rpow_const (fun θ hθ => Or.inl (ne_of_gt (hpos θ hθ)))

theorem continuousOn_rho6_box {α : ℝ} {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hd : d < π / 2) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => rho6 α i p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d) := by
  have hw : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) (Set.Icc a b ×ˢ Set.Icc c d) :=
    (continuousOn_w_box ha).comp continuousOn_fst (fun p hp => hp.1)
  have hs : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (continuousOn_sin_rpow_box (p := Work.Spaces.eta / 2) hc hd).comp continuousOn_snd
      (fun p hp => hp.2)
  have hs' : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)))
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (continuousOn_sin_rpow_box (p := -(Work.Spaces.gam α / 2)) hc hd).comp continuousOn_snd
      (fun p hp => hp.2)
  unfold rho6
  split_ifs with h
  · refine hw.div hs (fun p hp => ?_)
    have hsinn : 0 < Real.sin (2 * p.2) :=
      Real.sin_pos_of_pos_of_lt_pi (x := 2 * p.2) (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos])
    exact ne_of_gt (Real.rpow_pos_of_pos hsinn (Work.Spaces.eta / 2))
  · have : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1 *
        (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) (Set.Icc a b ×ˢ Set.Icc c d) :=
      hw.mul hs'
    simpa only [Work.Spaces.Wt, Work.Spaces.wTheta] using this

theorem continuousOn_rhoZ_box {α : ℝ} {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hd : d < π / 2) (i : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => rhoZ α i p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d) := by
  have hilt : ContinuousOn (fun p : ℝ × ℝ => p.1) (Set.Icc a b ×ˢ Set.Icc c d) := continuousOn_fst
  have h : ContinuousOn (fun p : ℝ × ℝ => p.1 * rho6 α i p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    hilt.mul (continuousOn_rho6_box (α := α) ha hc hd i)
  simpa only [rhoZ] using h

theorem continuousOn_rhoT_box {α : ℝ} {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c) (hd : d < π / 2) :
    ContinuousOn (fun p : ℝ × ℝ => rhoT α p.1 p.2) (Set.Icc a b ×ˢ Set.Icc c d) := by
  have hs : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) (Set.Icc a b ×ˢ Set.Icc c d) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have h : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2) * rho6 α 6 p.1 p.2)
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    hs.mul (continuousOn_rho6_box (α := α) (a := a) (b := b) (c := c) (d := d) ha hc hd 6)
  simpa only [rhoT] using h

theorem rhoZ_pos {α : ℝ} {i : ℕ} {z θ : ℝ} (hz : 0 < z) (ha : 0 < Real.sin (2 * θ)) :
    0 < rhoZ α i z θ := by
  have h1 : 0 < rho6 α i z θ := by
    unfold rho6
    split_ifs with h
    · exact div_pos (by
        simp only [Work.Spaces.w]
        positivity) (Real.rpow_pos_of_pos ha _)
    · simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
      exact mul_pos (by simp only [Work.Spaces.w]; positivity) (Real.rpow_pos_of_pos ha _)
  simpa only [rhoZ] using mul_pos hz h1

theorem rhoT_pos {α : ℝ} {z θ : ℝ} (hz : 0 < z) (ha : 0 < Real.sin (2 * θ)) :
    0 < rhoT α z θ := by
  have h1 : 0 < rho6 α 6 z θ := by
    unfold rho6
    simp only [Nat.succ_ne_zero 5, ite_false, Work.Spaces.Wt, Work.Spaces.wTheta]
    exact mul_pos (by simp only [Work.Spaces.w]; positivity) (Real.rpow_pos_of_pos ha _)
  simpa only [rhoT] using mul_pos ha h1


/-! ## The level-6 identities in `Fin`-sum form -/

theorem level6Z_eq_fin (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    level6Z α g z θ = ∑ k : Fin 6,
      (deriv (fun z' => Work.Spaces.mixed (5 - (k : ℕ)) (k : ℕ) g z' θ) z
        * (z * rho6 α (k : ℕ) z θ)) ^ 2 := by
  have h := (level6_identities α).2.1 g (z, θ)
  rw [h]
  exact (Fin.sum_univ_eq_sum_range (fun k : ℕ =>
    (deriv (fun z' => Work.Spaces.mixed (5 - k) k g z' θ) z * (z * rho6 α k z θ)) ^ 2) 6).symm

theorem level6T_eq_theta (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    level6T α g z θ = (deriv (fun θ' => Work.Spaces.mixed 0 5 g z θ') θ
        * (Real.sin (2 * θ) * rho6 α 6 z θ)) ^ 2 :=
  (level6_identities α).2.2 g (z, θ)

/-! ## The box bounds for the two level-6 majorants -/

theorem V6z_box_le {α : ℝ} {F : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hsmF : ∀ n k : ℕ, ContDiffOn ℝ k (Function.uncurry (F n)) Q0)
    (hcontF : ∀ n (j i : ℕ),
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i (F n) p.1 p.2) Q0)
    (hconv5 : ∀ᵐ p ∂(MeasureTheory.volume.restrict Q0), ∀ (j i : ℕ), j + i = 5 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (F n) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2)))
    {a b c d ε ε' : ℝ} (hab : a < b) (hcd : c < d) (hε : 0 < ε) (hε' : 0 < ε')
    (hlo : 0 < a - ε) (hcε : 0 < c - ε') (hdε : d + ε' < π / 2) :
    ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')), V6z α f p
      ≤ Filter.liminf (fun n => ∫⁻ p in (Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε') (d + ε')),
          ENNReal.ofReal (level6Z α (F n) p.1 p.2)) Filter.atTop := by
  classical
  have hbigQ : Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε') (d + ε') ⊆ Q0 :=
    box_subset_Q0 hlo hcε hdε
  have hsinn : ∀ θ ∈ Set.Icc (c - ε') (d + ε'), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (x := 2 * θ) (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hmain := lintegral_backwardDiffQuot_majorant_le_liminf_z
    (a := a - ε) (a' := a) (b' := b) (b := b + ε) (c := c - ε') (d := d + ε')
    (by linarith) (by linarith) (by linarith)
    (ι := Fin 6) (ρ := fun k : Fin 6 => rhoZ α (k : ℕ))
    (V := fun n k => Vslot F n (k : ℕ)) (W := fun k => Wslot f (k : ℕ))
    (fun k => continuousOn_rhoZ_box hlo hcε hdε (k : ℕ))
    (fun k z hz θ hθ => rhoZ_pos (by linarith [hz.1]) (hsinn θ hθ))
    (fun n k => by
      have hk : (k : ℕ) ≤ 5 := Nat.le_of_lt_succ k.isLt
      have h6 : ContDiffOn ℝ 6 (Function.uncurry (F n))
          (Set.Ioo (a - ε) (b + ε) ×ˢ Set.Ioo (c - ε') (d + ε')) :=
        (hsmF n 6).mono (by
          rintro ⟨z, θ⟩ ⟨hz, hθ⟩
          exact ⟨lt_trans hlo hz.1, lt_trans hcε hθ.1, lt_trans hθ.2 hdε⟩)
      exact Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
        (V := Set.Ioo (a - ε) (b + ε) ×ˢ Set.Ioo (c - ε') (d + ε'))
        (isOpen_Ioo.prod isOpen_Ioo) (k : ℕ) (5 - (k : ℕ)) 1
        (by rw [Nat.add_sub_of_le hk]) h6)
    (fun n k => (hcontF n (5 - (k : ℕ)) (k : ℕ)).mono hbigQ)
    (fun k => (aemeasurable_mixed_five hcontF hconv5
        (by
          have hk : (k : ℕ) ≤ 5 := Nat.le_of_lt_succ k.isLt
          rw [Nat.sub_add_cancel hk])).mono_measure
        (MeasureTheory.Measure.restrict_mono hbigQ (le_refl _)) |>.aestronglyMeasurable)
    (by
      have hae : ∀ᵐ p ∂(MeasureTheory.volume.restrict
          (Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε') (d + ε'))),
          ∀ (j i : ℕ), j + i = 5 →
            Filter.Tendsto (fun n => Work.Spaces.mixed j i (F n) p.1 p.2) Filter.atTop
              (nhds (Work.Spaces.mixed j i f p.1 p.2)) :=
        ae_restrict_box hlo hcε hdε hconv5
      refine hae.mono ?_
      intro p hp k
      exact hp (5 - (k : ℕ)) (k : ℕ)
        (by
          have hk : (k : ℕ) ≤ 5 := Nat.le_of_lt_succ k.isLt
          rw [Nat.sub_add_cancel hk]))
  calc ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')), V6z α f p
      = ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')), Filter.liminf (fun j : ℕ => ∑ k : Fin 6,
          ENNReal.ofReal (((Wslot f (k : ℕ) p.1 p.2 - Wslot f (k : ℕ) (p.1 - 1 / ((j : ℝ) + 1)) p.2)
            * ((j : ℝ) + 1) * rhoZ α (k : ℕ) p.1 p.2) ^ 2)) Filter.atTop :=
        lintegral_congr (fun p => V6z_eq' α f p)
    _ ≤ Filter.liminf (fun n => ∫⁻ p in (Set.Icc (a - ε) (b + ε) ×ˢ Set.Icc (c - ε') (d + ε')),
          ENNReal.ofReal (level6Z α (F n) p.1 p.2)) Filter.atTop := by
        refine hmain.trans (le_of_eq ?_)
        congr 1 with n
        refine lintegral_congr fun p => ?_
        rw [level6Z_eq_fin α (F n) p.1 p.2]
        rfl

theorem V6t_box_le {α : ℝ} {F : ℕ → ℝ → ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hsmF : ∀ n k : ℕ, ContDiffOn ℝ k (Function.uncurry (F n)) Q0)
    (hcontF : ∀ n (j i : ℕ),
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i (F n) p.1 p.2) Q0)
    (hconv5 : ∀ᵐ p ∂(MeasureTheory.volume.restrict Q0), ∀ (j i : ℕ), j + i = 5 →
      Filter.Tendsto (fun n => Work.Spaces.mixed j i (F n) p.1 p.2) Filter.atTop
        (nhds (Work.Spaces.mixed j i f p.1 p.2)))
    {a b c d ε' : ℝ} (hab : a < b) (hcd : c < d) (hε' : 0 < ε')
    (ha : 0 < a) (hcε : 0 < c - ε') (hdε : d + ε' < π / 2) :
    ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c d), V6t α f p
      ≤ Filter.liminf (fun n => ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')),
          ENNReal.ofReal (level6T α (F n) p.1 p.2)) Filter.atTop := by
  classical
  have hbigQ : Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε') ⊆ Q0 :=
    box_subset_Q0 ha hcε hdε
  have hsinn : ∀ θ ∈ Set.Icc (c - ε') (d + ε'), 0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (x := 2 * θ) (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hmain := lintegral_backwardDiffQuot_majorant_le_liminf_theta
    (a := a) (b := b) (c := c - ε') (c' := c) (d' := d) (d := d + ε')
    (by linarith) (by linarith) hab
    (ι := Fin 1) (ρ := fun _ : Fin 1 => rhoT α)
    (V := fun n _ => Vslot F n 5) (W := fun _ => Wslot f 5)
    (fun _ => continuousOn_rhoT_box ha hcε hdε)
    (fun _ z hz θ hθ => rhoT_pos (by linarith [hz.1]) (hsinn θ hθ))
    (fun n _ => by
      have h6 : ContDiffOn ℝ 6 (Function.uncurry (F n))
          (Set.Ioo a b ×ˢ Set.Ioo (c - ε') (d + ε')) :=
        (hsmF n 6).mono (by
          rintro ⟨z, θ⟩ ⟨hz, hθ⟩
          exact ⟨lt_trans ha hz.1, lt_trans hcε hθ.1, lt_trans hθ.2 hdε⟩)
      exact Work.FTS.CoercivityFix.Transfer.E2pkg.contDiffOn_uncurry_mixed_le
        (V := Set.Ioo a b ×ˢ Set.Ioo (c - ε') (d + ε'))
        (isOpen_Ioo.prod isOpen_Ioo) 5 0 1 (by norm_num) h6)
    (fun n _ => (hcontF n 0 5).mono hbigQ)
    (fun _ => (aemeasurable_mixed_five hcontF hconv5 (by norm_num : 0 + 5 = 5)).mono_measure
        (MeasureTheory.Measure.restrict_mono hbigQ (le_refl _)) |>.aestronglyMeasurable)
    (by
      have hae : ∀ᵐ p ∂(MeasureTheory.volume.restrict
          (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε'))),
          ∀ (j i : ℕ), j + i = 5 →
            Filter.Tendsto (fun n => Work.Spaces.mixed j i (F n) p.1 p.2) Filter.atTop
              (nhds (Work.Spaces.mixed j i f p.1 p.2)) :=
        ae_restrict_box ha hcε hdε hconv5
      refine hae.mono ?_
      intro p hp k
      exact hp 0 5 (by norm_num))
  calc ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c d), V6t α f p
      = ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc c d), Filter.liminf (fun j : ℕ => ∑ _k : Fin 1, ENNReal.ofReal
          (((Wslot f 5 p.1 p.2 - Wslot f 5 p.1 (p.2 - 1 / ((j : ℝ) + 1)))
            * ((j : ℝ) + 1) * rhoT α p.1 p.2) ^ 2)) Filter.atTop :=
        lintegral_congr (fun p => by rw [V6t_eq']; congr 1 with j; simp)
    _ ≤ Filter.liminf (fun n => ∫⁻ p in (Set.Icc a b ×ˢ Set.Icc (c - ε') (d + ε')),
          ENNReal.ofReal (level6T α (F n) p.1 p.2)) Filter.atTop := by
        refine hmain.trans (le_of_eq ?_)
        congr 1 with n
        refine lintegral_congr fun p => ?_
        rw [level6T_eq_theta α (F n) p.1 p.2]
        simp only [Vslot, rhoT, Fin.sum_univ_one]

end Work.FTS.StrongEps.LocUnif
