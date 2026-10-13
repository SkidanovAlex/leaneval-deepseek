import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.IsLocallyClosed
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.EComparison.EulerWeakFubini
import Submission.Work.FTS.StrongEps.EComparison.EulerWeakAffine
import Submission.Work.FTS.StrongEps.EComparison.ExistsTestfunSecondDeriv
import Submission.Work.FTS.StrongEps.EComparison.EulerWeakClassical
import Submission.Work.FTS.StrongEps.EComparison.EulerOdeZero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

/-!
# Rigidity of the weak Euler self-similar equation (`EulerWeakZero`)

The auxiliary lemmas below assemble the proof of `EulerWeakZero`:

* `affine_eq_of_ae_eq` -- two affine functions agreeing a.e. on a non degenerate interval agree.
* `exists_affine_of_forall_local` -- a function which is a.e. affine on every `(a,b) ⊆ (0,b)`
  is a.e. affine on `(0,b)` (consistency of the local affine data + countable cover).
* `exists_global_ode_solution` -- local classical solutions of the (Euler-type, second order)
  ODE on the intervals `(0,b)` glue to a global one on `(0,∞)`.
-/

/-- Two affine functions agreeing almost everywhere on a nondegenerate interval coincide. -/
lemma affine_eq_of_ae_eq {a b c₁ c₂ d₁ d₂ : ℝ} (hab : a < b)
    (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)), c₁ + c₂ * t = d₁ + d₂ * t) :
    c₁ = d₁ ∧ c₂ = d₂ := by
  have hcont₁ : ContinuousOn (fun t : ℝ => c₁ + c₂ * t) (Ioo a b) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  have hcont₂ : ContinuousOn (fun t : ℝ => d₁ + d₂ * t) (Ioo a b) :=
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  have heq : EqOn (fun t : ℝ => c₁ + c₂ * t) (fun t : ℝ => d₁ + d₂ * t) (Ioo a b) :=
    MeasureTheory.Measure.eqOn_Ioo_of_ae_eq volume h hcont₁ hcont₂
  have h1 : (2 * a + b) / 3 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have h2 : (a + 2 * b) / 3 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have e1 : c₁ + c₂ * ((2 * a + b) / 3) = d₁ + d₂ * ((2 * a + b) / 3) := heq h1
  have e2 : c₁ + c₂ * ((a + 2 * b) / 3) = d₁ + d₂ * ((a + 2 * b) / 3) := heq h2
  have ht : ((2 * a + b) / 3) - ((a + 2 * b) / 3) ≠ 0 := by
    intro hh; linarith
  have hc2 : c₂ = d₂ := by
    have hd : (c₂ - d₂) * (((2 * a + b) / 3) - ((a + 2 * b) / 3)) = 0 := by
      linear_combination e1 - e2
    rcases mul_eq_zero.mp hd with h | h
    · linarith
    · exact absurd h ht
  have hc1 : c₁ = d₁ := by linear_combination e1 - hc2 * ((2 * a + b) / 3)
  exact ⟨hc1, hc2⟩

/-- If a function is a.e. affine on every subinterval `(a,b) ⊆ (0,b)` (with the same ambient `b`),
then the affine representation is in fact global: there is a single pair `(c₁,c₂)` with
`F t = c₁ + c₂ t` for a.e. `t ∈ (0,b)`. -/
lemma exists_affine_of_forall_local {b : ℝ} (hb : 0 < b) {F : ℝ → ℝ}
    (h : ∀ a ∈ Ioo (0 : ℝ) b,
      ∃ c₁ c₂ : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo a b)), F t = c₁ + c₂ * t) :
    ∃ c₁ c₂ : ℝ, ∀ᵐ t ∂(volume.restrict (Ioo 0 b)), F t = c₁ + c₂ * t := by
  classical
  have hpair : ∀ a ∈ Ioo (0 : ℝ) b,
      ∃ p : ℝ × ℝ, ∀ᵐ t ∂(volume.restrict (Ioo a b)), F t = p.1 + p.2 * t := by
    rintro a ha
    obtain ⟨c₁, c₂, hc⟩ := h a ha
    exact ⟨(c₁, c₂), hc⟩
  have hb2 : (b / 2) ∈ Ioo (0 : ℝ) b := ⟨by linarith, by linarith⟩
  obtain ⟨p, hp_spec⟩ := hpair (b / 2) hb2
  have hcons : ∀ a ∈ Ioo (0 : ℝ) b,
      ∀ᵐ t ∂(volume.restrict (Ioo a b)), F t = p.1 + p.2 * t := by
    rintro a ⟨ha0, hab⟩
    obtain ⟨q, hq⟩ := hpair a ⟨ha0, hab⟩
    rcases le_or_gt a (b / 2) with hle | hlt
    · have hsub : Ioo (b / 2) b ⊆ Ioo a b := fun t ht => ⟨by linarith [ht.1, hle], ht.2⟩
      have hq' : ∀ᵐ t ∂(volume.restrict (Ioo (b / 2) b)), F t = q.1 + q.2 * t :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub hq
      have hp' : ∀ᵐ t ∂(volume.restrict (Ioo (b / 2) b)), F t = p.1 + p.2 * t := hp_spec
      have hae : ∀ᵐ t ∂(volume.restrict (Ioo (b / 2) b)), q.1 + q.2 * t = p.1 + p.2 * t := by
        filter_upwards [hq', hp'] with t h1 h2
        rw [← h1, h2]
      have hqp := affine_eq_of_ae_eq (a := b / 2) (b := b) (by linarith) hae
      rwa [hqp.1, hqp.2] at hq
    · have hsub : Ioo a b ⊆ Ioo (b / 2) b := fun t ht => ⟨by linarith [hlt.le, ht.1], ht.2⟩
      have hp' : ∀ᵐ t ∂(volume.restrict (Ioo a b)), F t = p.1 + p.2 * t :=
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub hp_spec
      have hae : ∀ᵐ t ∂(volume.restrict (Ioo a b)), q.1 + q.2 * t = p.1 + p.2 * t := by
        filter_upwards [hq, hp'] with t h1 h2
        rw [← h1, h2]
      have hqp := affine_eq_of_ae_eq hab hae
      rwa [hqp.1, hqp.2] at hq
  refine ⟨p.1, p.2, ?_⟩
  have hfin : ∀ n : ℕ, ∀ᵐ t ∂(volume.restrict (Ioo (b / ((n : ℝ) + 2)) b)),
      F t = p.1 + p.2 * t := by
    intro n
    have h2n : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    refine hcons _ ⟨div_pos hb h2n, ?_⟩
    rw [div_lt_iff₀ h2n]
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    nlinarith [hb, hn]
  have hunion : Ioo (0 : ℝ) b = ⋃ n : ℕ, Ioo (b / ((n : ℝ) + 2)) b := by
    ext t
    simp only [mem_iUnion, mem_Ioo]
    constructor
    · rintro ⟨ht0, htb⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (b / t)
      refine ⟨n, ?_, htb⟩
      rw [div_lt_iff₀ (by positivity)]
      have h₁ := (div_lt_iff₀ ht0).mp hn
      nlinarith
    · rintro ⟨n, hn1, hn2⟩
      exact ⟨lt_trans (by positivity) hn1, hn2⟩
  rw [hunion, MeasureTheory.ae_restrict_iUnion_iff]
  exact hfin

/-- Local classical solutions of the Euler-type second order ODE on the intervals `(0,b)` glue to a
global classical solution on `(0,∞)`. -/
lemma exists_global_ode_solution {α L : ℝ} {W : ℝ → ℝ}
    (h : ∀ b : ℝ, 0 < b → ∃ V : ℝ → ℝ, ContDiffOn ℝ 2 V (Ioo 0 b) ∧
      (∀ t ∈ Ioo 0 b, α ^ 2 * t ^ 2 * deriv (deriv V) t + α * (3 * α - 5) * t * deriv V t
        + (α ^ 2 - 5 * α - L) * V t = 0) ∧ V =ᵐ[volume.restrict (Ioo 0 b)] W) :
    ∃ V : ℝ → ℝ, ContDiffOn ℝ 2 V (Ioi 0) ∧
      (∀ t ∈ Ioi 0, α ^ 2 * t ^ 2 * deriv (deriv V) t + α * (3 * α - 5) * t * deriv V t
        + (α ^ 2 - 5 * α - L) * V t = 0) ∧ V =ᵐ[volume.restrict (Ioi 0)] W := by
  classical
  let Vb : ℝ → ℝ → ℝ := fun b => if hb : 0 < b then Classical.choose (h b hb) else 0
  have hVb : ∀ b (hb : 0 < b), ContDiffOn ℝ 2 (Vb b) (Ioo 0 b) ∧
      (∀ t ∈ Ioo 0 b, α ^ 2 * t ^ 2 * deriv (deriv (Vb b)) t + α * (3 * α - 5) * t * deriv (Vb b) t
        + (α ^ 2 - 5 * α - L) * Vb b t = 0) ∧ Vb b =ᵐ[volume.restrict (Ioo 0 b)] W := by
    intro b hb
    have := Classical.choose_spec (h b hb)
    simpa only [Vb, dif_pos hb] using this
  have hcons : ∀ b b' (hb : 0 < b) (hb' : 0 < b'), EqOn (Vb b) (Vb b') (Ioo 0 (min b b')) := by
    intro b b' hb hb'
    have h1 : ∀ᵐ z ∂(volume.restrict (Ioo 0 b)), Vb b z = W z := (hVb b hb).2.2
    have h2 : ∀ᵐ z ∂(volume.restrict (Ioo 0 b')), Vb b' z = W z := (hVb b' hb').2.2
    have hsub1 : Ioo 0 (min b b') ⊆ Ioo 0 b :=
      fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left b b')⟩
    have hsub2 : Ioo 0 (min b b') ⊆ Ioo 0 b' :=
      fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right b b')⟩
    have h1' : ∀ᵐ z ∂(volume.restrict (Ioo 0 (min b b'))), Vb b z = W z :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub1 h1
    have h2' : ∀ᵐ z ∂(volume.restrict (Ioo 0 (min b b'))), Vb b' z = W z :=
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub2 h2
    have hu : (fun z => Vb b z) =ᵐ[volume.restrict (Ioo 0 (min b b'))] (fun z => Vb b' z) := by
      filter_upwards [h1', h2'] with z hz1 hz2
      rw [hz1, hz2]
    exact MeasureTheory.Measure.eqOn_Ioo_of_ae_eq volume hu
      ((hVb b hb).1.continuousOn.mono hsub1) ((hVb b' hb').1.continuousOn.mono hsub2)
  let V : ℝ → ℝ := fun z => if hz : 0 < z then Vb (z + 1) z else 0
  have hV_eq : ∀ z ∈ Ioi (0 : ℝ), EqOn V (Vb (z + 1)) (Ioo 0 (z + 1)) := by
    intro z hz
    refine fun z' hz' => ?_
    have hz'0 : 0 < z' := hz'.1
    have hz'z : z' < z + 1 := hz'.2
    have h1 : V z' = Vb (z' + 1) z' := by
      show (if h : 0 < z' then Vb (z' + 1) z' else 0) = Vb (z' + 1) z'
      rw [dif_pos hz'0]
    have h2 : Vb (z' + 1) z' = Vb (z + 1) z' := by
      have hmem : z' ∈ Ioo 0 (min (z' + 1) (z + 1)) := by
        refine ⟨hz'0, ?_⟩
        exact lt_min (by linarith) hz'z
      exact hcons (z' + 1) (z + 1) (by linarith) (by linarith) hmem
    rw [h1, h2]
  have hV_cd : ContDiffOn ℝ 2 V (Ioi 0) := by
    intro z hz
    have hz0 : (0 : ℝ) < z := hz
    rw [contDiffWithinAt_iff_contDiffAt (isOpen_Ioi.mem_nhds hz)]
    refine (ContDiffOn.congr (hVb (z + 1) (by linarith)).1
        (fun w hw => hV_eq z hz hw)).contDiffAt ?_
    exact isOpen_Ioo.mem_nhds ⟨hz0, by linarith⟩
  have hV_deriv1 : ∀ z ∈ Ioi (0 : ℝ), ∀ w ∈ Ioo 0 (z + 1),
      deriv V w = deriv (Vb (z + 1)) w := by
    intro z hz w hw
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hw) (fun w' hw' => hV_eq z hz hw'))
  have hV_deriv2 : ∀ z ∈ Ioi (0 : ℝ), ∀ w ∈ Ioo 0 (z + 1),
      deriv (deriv V) w = deriv (deriv (Vb (z + 1))) w := by
    intro z hz w hw
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hw) (fun w' hw' => hV_deriv1 z hz w' hw'))
  have hV_ode : ∀ t ∈ Ioi (0 : ℝ), α ^ 2 * t ^ 2 * deriv (deriv V) t
      + α * (3 * α - 5) * t * deriv V t + (α ^ 2 - 5 * α - L) * V t = 0 := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have htU : t ∈ Ioo 0 (t + 1) := ⟨ht0, by linarith⟩
    have hspec := (hVb (t + 1) (by linarith)).2.1 t htU
    rw [hV_deriv2 t ht t htU, hV_deriv1 t ht t htU, hV_eq t ht htU]
    exact hspec
  have hV_ae : ∀ᵐ z ∂(volume.restrict (Ioi 0)), V z = W z := by
    have hunion : Ioi (0 : ℝ) = ⋃ n : ℕ, Ioo (0 : ℝ) ((n : ℝ) + 1) := by
      ext t
      simp only [mem_iUnion, mem_Ioi, mem_Ioo]
      constructor
      · intro ht
        obtain ⟨n, hn⟩ := exists_nat_gt t
        exact ⟨n, ht, by linarith⟩
      · rintro ⟨n, hn1, -⟩
        exact hn1
    rw [hunion, MeasureTheory.ae_restrict_iUnion_iff]
    intro n
    have hpoint : ∀ w ∈ Ioo (0 : ℝ) ((n : ℝ) + 1), V w = Vb ((n : ℝ) + 1) w := by
      intro w hw
      have hw0 : 0 < w := hw.1
      have h1 : V w = Vb (w + 1) w := by
        show (if h : 0 < w then Vb (w + 1) w else 0) = Vb (w + 1) w
        rw [dif_pos hw0]
      have h2 : Vb (w + 1) w = Vb ((n : ℝ) + 1) w := by
        have hmem : w ∈ Ioo 0 (min (w + 1) ((n : ℝ) + 1)) := by
          refine ⟨hw0, ?_⟩
          exact lt_min (by linarith) hw.2
        exact hcons (w + 1) ((n : ℝ) + 1) (by linarith) (by positivity) hmem
      rw [h1, h2]
    have h1 : ∀ᵐ z ∂(volume.restrict (Ioo 0 ((n : ℝ) + 1))), V z = Vb ((n : ℝ) + 1) z :=
      (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).2
        (Filter.Eventually.of_forall fun w hw => hpoint w hw)
    have h2 : ∀ᵐ z ∂(volume.restrict (Ioo 0 ((n : ℝ) + 1))),
        Vb ((n : ℝ) + 1) z = W z := (hVb ((n : ℝ) + 1) (by positivity)).2.2
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz1, hz2]
  exact ⟨V, hV_cd, hV_ode, hV_ae⟩

/-- The auxiliary modulus identity: `z^(2p) * z^(-4-2p) = z^(-4)` for `z > 0`. -/
private lemma rpow_two_mul_shift {z p : ℝ} (hz : 0 < z) :
    z ^ (2 * p) * z ^ (-4 - 2 * p) = z ^ (-4 : ℝ) := by
  rw [← Real.rpow_add hz]
  ring_nf

/-- `(z^p)^2 = z^(2p)` for `z ≥ 0`. -/
private lemma sq_rpow {z p : ℝ} (hz : 0 ≤ z) : (z ^ p) ^ 2 = z ^ (2 * p) := by
  rw [← Real.rpow_natCast (z ^ p) 2, ← Real.rpow_mul hz]
  ring_nf

theorem EulerWeakZero {α L : ℝ} (hα : 0 < α) {u : ℝ → ℝ}
    (hu : MeasureTheory.LocallyIntegrableOn u (Set.Ioi 0))
    (hweak : ∀ ρ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ρ) → HasCompactSupport ρ →
      tsupport ρ ⊆ Set.Ioi 0 →
      (∫ z in Set.Ioi 0, z ^ ((5 - α) / α) * (L * ρ z
        - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)) * u z) = 0)
    (hint : MeasureTheory.IntegrableOn (fun z => (u z) ^ 2 * z ^ (-4 : ℝ)) (Set.Ioi 0)) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), u z = 0 := by
  set W : ℝ → ℝ := fun z => u z * z ^ ((5 - α) / α) with hWdef
  have hW : MeasureTheory.LocallyIntegrableOn W (Set.Ioi 0) := by
    have hcont : ContinuousOn (fun z : ℝ => z ^ ((5 - α) / α)) (Set.Ioi 0) :=
      continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz))
    simpa only [hWdef] using hu.mul_continuousOn hcont isOpen_Ioi.isLocallyClosed
  have hweakW : ∀ ρ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n ρ) → HasCompactSupport ρ →
      tsupport ρ ⊆ Set.Ioi 0 →
      (∫ z in Set.Ioi 0, W z * (L * ρ z
        - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z))) = 0 := by
    intro ρ hρ hρc hsupp
    have h := hweak ρ hρ hρc hsupp
    have hcongr : (∫ z in Set.Ioi 0, W z * (L * ρ z
        - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)))
        = ∫ z in Set.Ioi 0, z ^ ((5 - α) / α) * (L * ρ z
        - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z)) * u z := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with z
      simp only [hWdef]
      ring
    rw [hcongr, h]
  -- Step 1: the function figuring in the local affine identity is a.e. affine on `(0,b)`.
  have key : ∀ b : ℝ, 0 < b → ∃ c₁ c₂ : ℝ, ∀ᵐ t ∂(volume.restrict (Set.Ioo 0 b)),
      -(α ^ 2 * t ^ 2 * W t) - α * (5 + α) * (∫ z in t..b, W z * z)
        + L * (∫ z in t..b, (z - t) * W z) = c₁ + c₂ * t := by
    intro b hb
    refine exists_affine_of_forall_local hb ?_
    intro a ha
    obtain ⟨ha0, hab⟩ := ha
    set F : ℝ → ℝ := fun t => -(α ^ 2 * t ^ 2 * W t) - α * (5 + α) * (∫ z in t..b, W z * z)
        + L * (∫ z in t..b, (z - t) * W z) with hFdef
    have hFint : MeasureTheory.LocallyIntegrableOn F (Set.Ioo a b) := by
      have hIoo0 : Set.Ioo a b ⊆ Set.Ioi 0 := fun z hz => lt_trans ha0 hz.1
      have hprod : MeasureTheory.LocallyIntegrableOn (fun t : ℝ => W t * t ^ 2) (Set.Ioo a b) :=
        (hW.mono_set hIoo0).mul_continuousOn (by fun_prop) isLocallyClosed_Ioo
      have hA : MeasureTheory.LocallyIntegrableOn (fun t : ℝ => -(α ^ 2 * t ^ 2 * W t))
          (Set.Ioo a b) := by
        have h1 : MeasureTheory.LocallyIntegrableOn (fun t : ℝ => (W t * t ^ 2) * (-(α ^ 2)))
            (Set.Ioo a b) := hprod.mul_continuousOn continuousOn_const isLocallyClosed_Ioo
        refine h1.congr ?_
        filter_upwards with t
        ring
      have hInt1 : MeasureTheory.IntegrableOn W (Set.uIcc a b) :=
        hW.integrableOn_compact_subset (fun z hz => by
          rcases Set.mem_uIcc.mp hz with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact lt_of_lt_of_le ha0 h1
          · exact lt_of_lt_of_le (lt_trans ha0 hab) h1) isCompact_uIcc
      have hInt2 : MeasureTheory.IntegrableOn (fun z : ℝ => W z * z) (Set.uIcc a b) :=
        hInt1.mul_continuousOn continuous_id.continuousOn isCompact_uIcc
      have hmem : Set.Ioo a b ⊆ Set.uIcc a b :=
        fun z hz => Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
      have hcontA : ContinuousOn (fun t : ℝ => ∫ z in t..b, W z * z) (Set.Ioo a b) :=
        (intervalIntegral.continuousOn_primitive_interval_left hInt2).mono hmem
      have hcontC : ContinuousOn (fun t : ℝ => ∫ z in t..b, W z) (Set.Ioo a b) :=
        (intervalIntegral.continuousOn_primitive_interval_left hInt1).mono hmem
      have hB : Set.EqOn (fun t : ℝ => ∫ z in t..b, (z - t) * W z)
          (fun t : ℝ => (∫ z in t..b, W z * z) - t * (∫ z in t..b, W z)) (Set.Ioo a b) := by
        intro t ht
        change (∫ z in t..b, (z - t) * W z)
          = (∫ z in t..b, W z * z) - t * (∫ z in t..b, W z)
        have hsub : Set.uIcc t b ⊆ Set.uIcc a b := by
          rw [Set.uIcc_of_le (le_of_lt ht.2), Set.uIcc_of_le (le_of_lt hab)]
          intro z hz
          exact ⟨le_trans (le_of_lt ht.1) hz.1, hz.2⟩
        have h1 : (∫ z in t..b, (z - t) * W z) = ∫ z in t..b, (W z * z - t * W z) := by
          refine intervalIntegral.integral_congr ?_
          intro z hz
          ring
        have h2 : IntervalIntegrable (fun z : ℝ => t * W z) volume t b :=
          IntervalIntegrable.congr (f := fun z : ℝ => W z * t) (fun z hz => by ring)
            (((hInt1.mono_set hsub).mul_continuousOn continuousOn_const isCompact_uIcc).intervalIntegrable)
        rw [h1, intervalIntegral.integral_sub ((hInt2.mono_set hsub).intervalIntegrable) h2,
          intervalIntegral.integral_const_mul]
      have hcontB : ContinuousOn (fun t : ℝ => ∫ z in t..b, (z - t) * W z) (Set.Ioo a b) := by
        refine ContinuousOn.congr (hcontA.sub (continuousOn_id.mul hcontC)) ?_
        intro t ht
        change (∫ z in t..b, (z - t) * W z)
          = (∫ z in t..b, W z * z) - t * (∫ z in t..b, W z)
        exact hB ht
      have hR : MeasureTheory.LocallyIntegrableOn (fun t : ℝ => - α * (5 + α) * (∫ z in t..b, W z * z)
            + L * (∫ z in t..b, (z - t) * W z)) (Set.Ioo a b) :=
        ((hcontA.const_mul (- α * (5 + α))).add (hcontB.const_mul L)).locallyIntegrableOn
          measurableSet_Ioo
      have hFeq : F = fun t : ℝ => -(α ^ 2 * t ^ 2 * W t)
          + (- α * (5 + α) * (∫ z in t..b, W z * z) + L * (∫ z in t..b, (z - t) * W z)) := by
        funext t
        rw [hFdef]
        ring
      rw [hFeq]
      exact hA.add hR
    refine EulerWeakAffine hab hFint ?_
    intro ψ hψ hψc hsupp h1 h2
    obtain ⟨ρ, hρ, hρc, hρs, hρd⟩ := ExistsTestfunSecondDeriv hab hψ hψc hsupp h1 h2
    have hsupp0 : tsupport ρ ⊆ Set.Ioi 0 := fun z hz => lt_trans ha0 (hρs hz).1
    have hfub := EulerWeakFubini (α := α) (L := L) hW ha0 hab hρ hρc hρs
    have hzero : (∫ z in Set.Ioi 0, W z * (L * ρ z
        - (α ^ 2 * z ^ 2 * deriv (deriv ρ) z + α * (5 + α) * z * deriv ρ z))) = 0 :=
      hweakW ρ hρ hρc hsupp0
    rw [hzero] at hfub
    have hgoal : (∫ t in a..b, deriv (deriv ρ) t * F t) = 0 := by
      rw [hFdef]
      exact hfub.symm
    rw [show (∫ t in a..b, ψ t * F t) = ∫ t in a..b, deriv (deriv ρ) t * F t from by
      refine intervalIntegral.integral_congr ?_
      intro t ht
      change ψ t * F t = deriv (deriv ρ) t * F t
      rw [hρd t]]
    exact hgoal
  -- Step 2: classical local solutions of the Euler-type ODE.
  have key2 : ∀ b : ℝ, 0 < b → ∃ V : ℝ → ℝ, ContDiffOn ℝ 2 V (Set.Ioo 0 b) ∧
      (∀ t ∈ Set.Ioo 0 b, α ^ 2 * t ^ 2 * deriv (deriv V) t + α * (3 * α - 5) * t * deriv V t
        + (α ^ 2 - 5 * α - L) * V t = 0) ∧ V =ᵐ[volume.restrict (Set.Ioo 0 b)] W := by
    intro b hb
    obtain ⟨c₁, c₂, hc⟩ := key b hb
    exact EulerWeakClassical (α := α) (L := L) hα hb hW hc
  obtain ⟨V, hVcd, hVode, hVae⟩ := exists_global_ode_solution key2
  -- Step 3: the weighted integrability of `V`.
  have hWint : MeasureTheory.IntegrableOn (fun z : ℝ => (W z) ^ 2 * z ^ (-((10 + 2 * α) / α)))
      (Set.Ioi 0) := by
    refine hint.congr_fun ?_ measurableSet_Ioi
    intro z hz
    have hz0 : 0 < z := hz
    have hMsplit : -((10 + 2 * α) / α) = -4 - 2 * ((5 - α) / α) := by
      field_simp
      ring
    rw [hWdef]
    change (u z) ^ 2 * z ^ (-4 : ℝ)
      = (u z * z ^ ((5 - α) / α)) ^ 2 * z ^ (-((10 + 2 * α) / α))
    rw [hMsplit, mul_pow, sq_rpow (le_of_lt hz0), mul_assoc, rpow_two_mul_shift hz0]
  have hVint : MeasureTheory.IntegrableOn (fun z : ℝ => (V z) ^ 2 * z ^ (-((10 + 2 * α) / α)))
      (Set.Ioi 0) := by
    refine hWint.congr_fun_ae ?_
    filter_upwards [hVae] with z hz
    rw [← hz]
  -- Step 4: `V` vanishes, hence so does `u`.
  have hν : (0 : ℝ) < (10 + α) / α := div_pos (by linarith) hα
  have hode : ∀ z ∈ Set.Ioi 0, z ^ 2 * deriv (deriv V) z + ((3 * α - 5) / α) * z * deriv V z
      + ((α ^ 2 - 5 * α - L) / α ^ 2) * V z = 0 := by
    intro z hz
    have h := hVode z hz
    have hα2 : α ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hα)
    field_simp
    linarith [h]
  have hVint' : MeasureTheory.IntegrableOn
      (fun z : ℝ => (V z) ^ 2 * z ^ ((-1 : ℝ) - (10 + α) / α)) (Set.Ioi 0) := by
    convert hVint using 2
    rw [show (-((10 + 2 * α) / α)) = (-1 : ℝ) - (10 + α) / α from by field_simp; ring]
  have hV0 : ∀ z ∈ Set.Ioi 0, V z = 0 :=
    EulerOdeZero (p := (3 * α - 5) / α) (q := (α ^ 2 - 5 * α - L) / α ^ 2)
      (ν := (10 + α) / α) hν hVcd hode hVint'
  have hW0 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), W z = 0 := by
    filter_upwards [hVae, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzmem
    rw [← hz]
    exact hV0 z hzmem
  filter_upwards [hW0, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzmem
  have hz0 : (0 : ℝ) < z := hzmem
  rw [hWdef] at hz
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt (Real.rpow_pos_of_pos hz0 _))

end Work.FTS.StrongEps.EComparison
