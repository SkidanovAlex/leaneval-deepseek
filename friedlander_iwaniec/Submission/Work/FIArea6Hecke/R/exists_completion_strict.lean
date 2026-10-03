import Mathlib
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea5.S16Hecke.thetaOdd_poisson
import Submission.Work.FIArea5.S16Hecke.thetaOdd_eq_unitSum_mul_thetaHol
import Submission.Work.FIArea5.S16Hecke.mellin_thetaHol
import Submission.Work.FIArea5.S16Hecke.twistAux
import Submission.Work.FIArea5.S16Hecke.twist_unitSum
import Submission.Work.FIArea5.S16Hecke.thetaHol_twist_eq
import Submission.Work.FIArea6Hecke.S16HeckeCompletionPrimitive
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea6Hecke.R.A6HeckeDual
import Submission.Work.FIArea6Hecke.R.gaussSum_zero_of_nontrivial
import Submission.Work.FIArea6Hecke.R.thetaHol_zero_one_div
import Submission.Work.FIArea6Hecke.R.continuousOn_thetaDual
import Submission.Work.FIArea6Hecke.R.thetaDual_decay
import Submission.Work.FIArea6Hecke.R.thetaHol_zero_basic

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-! ## the dual-side function -/

/-- The dual partner of `thetaHol χ 0` under Poisson summation. -/
def thetaDualG (d : ℕ) (chi : GaussianInt → ℂ) : ℝ → ℂ :=
  fun x => (Work.FIArea5.S16Hecke.unitSum chi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2)) *
    thetaDual d chi (x / (16 * (d : ℝ) ^ 2))

/-! ## exponential decay implies `O (· ^ r)` -/

lemma isBigO_rpow_of_exp_decay {F : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (h : ∃ C u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ‖F u‖ ≤ C * Real.exp (-a * u)) (r : ℝ) :
    F =O[Filter.atTop] (fun x : ℝ => x ^ r) := by
  obtain ⟨C, u₀, hu₀, hC⟩ := h
  have hCnn : 0 ≤ C := by
    have h1 := hC u₀ le_rfl
    have h2 := Real.exp_pos (-a * u₀)
    nlinarith [norm_nonneg (F u₀), h1, h2]
  by_cases hr : 0 ≤ r
  · refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Filter.eventually_ge_atTop (max u₀ 1)] with u hu
    have h1 : ‖F u‖ ≤ C * Real.exp (-a * u) := hC u (le_trans (le_max_left _ _) hu)
    have hu1 : (1 : ℝ) ≤ u := le_trans (le_max_right _ _) hu
    have hle1 : Real.exp (-a * u) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_pos ha (lt_of_lt_of_le zero_lt_one hu1)])
    have hrp : (1 : ℝ) ≤ u ^ r := Real.one_le_rpow hu1 hr
    have hnorm : ‖(fun x : ℝ => x ^ r) u‖ = u ^ r :=
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) r)
    calc ‖F u‖ ≤ C * Real.exp (-a * u) := h1
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hle1 hCnn
      _ ≤ C * u ^ r := by rw [mul_one]; exact le_mul_of_one_le_right hCnn hrp
      _ = C * ‖(fun x : ℝ => x ^ r) u‖ := by rw [hnorm]
  · have hr' : r < 0 := not_le.mp hr
    have ht : 0 < -r := neg_pos.mpr hr'
    have htend := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-r) a ha
    have hev : ∀ᶠ u : ℝ in Filter.atTop, u ^ (-r) * Real.exp (-a * u) ≤ 1 :=
      htend.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [Filter.eventually_ge_atTop (max (max u₀ M) 1)] with u hu
    have hu₀' : u₀ ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
    have hM' : M ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
    have hpos : 0 < u := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hu)
    have h1 : ‖F u‖ ≤ C * Real.exp (-a * u) := hC u hu₀'
    have h2 : u ^ (-r) * Real.exp (-a * u) ≤ 1 := hM u hM'
    have h3 : Real.exp (-a * u) ≤ u ^ r := by
      have hupr : 0 < u ^ (-r) := Real.rpow_pos_of_pos hpos _
      have hdiv : Real.exp (-a * u) ≤ 1 / u ^ (-r) := by
        rw [le_div_iff₀ hupr]; linarith
      rwa [one_div, ← Real.rpow_neg hpos.le, neg_neg] at hdiv
    calc ‖F u‖ ≤ C * Real.exp (-a * u) := h1
      _ ≤ C * u ^ r := mul_le_mul_of_nonneg_left h3 hCnn
      _ = C * ‖(fun x : ℝ => x ^ r) u‖ := by rw [Real.norm_of_nonneg (Real.rpow_nonneg hpos.le r)]

/-! ## the completion for a strict character with non-zero unit sum -/

theorem completion_of_unitSum_ne_zero {d : ℕ} (hd : 1 ≤ d) {psi : GaussianInt → ℂ}
    (hpsi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d psi)
    (hU : Work.FIArea5.S16Hecke.unitSum psi 0 ≠ 0)
    (h0 : Work.FIArea5.S16Hecke.gaussSum d psi 0 = 0) :
    ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      ∀ s : ℂ, 1 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d 0 s * Work.FIArea5.S16Hecke.heckeLSeries psi 0 s := by
  have hb : ∀ z : GaussianInt, ‖psi z‖ ≤ 1 := hpsi.1.2.2.1
  have h4dpos : (0 : ℝ) < 4 * (d : ℝ) := by
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have h16 : (0 : ℝ) < 16 * (d : ℝ) ^ 2 := by positivity
  have hdd : ((d : ℝ) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.mpr ?_
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    exact ne_of_gt hdR
  have h4dne : ((4 * (d : ℝ)) : ℂ) ≠ 0 := mul_ne_zero (by norm_num) hdd
  obtain ⟨hf_cont, hf_dec⟩ := thetaHol_zero_basic hd hpsi
  have hf_int : MeasureTheory.LocallyIntegrableOn
      (fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol psi 0 u) (Set.Ioi 0) :=
    hf_cont.locallyIntegrableOn measurableSet_Ioi
  have htd_cont : ContinuousOn (thetaDual d psi) (Set.Ioi 0) := continuousOn_thetaDual d hb
  have hg_cont : ContinuousOn (thetaDualG d psi) (Set.Ioi 0) := by
    have hscale : Continuous (fun x : ℝ => x / (16 * (d : ℝ) ^ 2)) := continuous_id.div_const _
    have hmaps : Set.MapsTo (fun x : ℝ => x / (16 * (d : ℝ) ^ 2)) (Set.Ioi 0) (Set.Ioi 0) := by
      intro x hx
      simp only [Set.mem_Ioi] at hx ⊢
      positivity
    have hcomp : ContinuousOn (fun x : ℝ => thetaDual d psi (x / (16 * (d : ℝ) ^ 2)))
        (Set.Ioi 0) := htd_cont.comp hscale.continuousOn hmaps
    unfold thetaDualG
    exact continuousOn_const.mul hcomp
  have hg_int : MeasureTheory.LocallyIntegrableOn (thetaDualG d psi) (Set.Ioi 0) :=
    hg_cont.locallyIntegrableOn measurableSet_Ioi
  obtain ⟨C, hC⟩ := thetaDual_decay hd hb h0
  have hg_dec : ∃ C' u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, u₀ ≤ u →
      ‖thetaDualG d psi u‖ ≤ C' * Real.exp (-(Real.pi / (16 * (d : ℝ) ^ 2)) * u) := by
    refine ⟨‖(Work.FIArea5.S16Hecke.unitSum psi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2))‖ * C,
      16 * (d : ℝ) ^ 2, h16, ?_⟩
    intro u hu
    have harg : 1 ≤ u / (16 * (d : ℝ) ^ 2) := by
      rw [le_div_iff₀ h16]; linarith
    have h1 : ‖thetaDual d psi (u / (16 * (d : ℝ) ^ 2))‖
        ≤ C * Real.exp (-Real.pi * (u / (16 * (d : ℝ) ^ 2))) := hC _ harg
    rw [thetaDualG]
    calc ‖(Work.FIArea5.S16Hecke.unitSum psi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2)) *
          thetaDual d psi (u / (16 * (d : ℝ) ^ 2))‖
        = ‖(Work.FIArea5.S16Hecke.unitSum psi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2))‖ *
            ‖thetaDual d psi (u / (16 * (d : ℝ) ^ 2))‖ := norm_mul _ _
      _ ≤ ‖(Work.FIArea5.S16Hecke.unitSum psi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2))‖ *
            (C * Real.exp (-Real.pi * (u / (16 * (d : ℝ) ^ 2)))) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (‖(Work.FIArea5.S16Hecke.unitSum psi 0)⁻¹ * (1 / (16 * (d : ℝ) ^ 2))‖ * C) *
            Real.exp (-(Real.pi / (16 * (d : ℝ) ^ 2)) * u) := by
          rw [show -Real.pi * (u / (16 * (d : ℝ) ^ 2)) = -(Real.pi / (16 * (d : ℝ) ^ 2)) * u by ring]
          ring
  have hfe : ∀ x ∈ Set.Ioi (0 : ℝ),
      (fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol psi 0 u) (1 / x)
        = (1 * ((x ^ (1 : ℝ) : ℝ) : ℂ)) • (fun y : ℝ => thetaDualG d psi y) x := by
    intro x hx
    have hx0 : 0 < x := hx
    change Work.FIArea5.S16Hecke.thetaHol psi 0 (1 / x)
      = (1 * ((x ^ (1 : ℝ) : ℝ) : ℂ)) • thetaDualG d psi x
    rw [thetaHol_zero_one_div hd hpsi hU hx0]
    simp only [Real.rpow_one, one_mul, smul_eq_mul]
    rw [thetaDualG]
  let P : WeakFEPair ℂ :=
    { f := fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol psi 0 u
      g := thetaDualG d psi
      k := 1
      ε := 1
      f₀ := 0
      g₀ := 0
      hf_int := hf_int
      hg_int := hg_int
      hk := one_pos
      hε := one_ne_zero
      h_feq := hfe
      hf_top := fun r => by
        simpa only [sub_zero] using isBigO_rpow_of_exp_decay Real.pi_pos hf_dec r
      hg_top := fun r => by
        simpa only [sub_zero] using
          isBigO_rpow_of_exp_decay (show (0 : ℝ) < Real.pi / (16 * (d : ℝ) ^ 2) by positivity)
            hg_dec r }
  have hP : IsStrongFEPair P := ⟨rfl, rfl⟩
  have hΛeq : P.Λ = mellin (fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol psi 0 u) := hP.Λ_eq
  refine ⟨fun s => ((4 * (d : ℝ)) : ℂ) ^ s * P.Λ s, ?_, ?_⟩
  · refine DifferentiableOn.analyticOn ?_ isOpen_univ
    intro s _
    exact ((differentiableAt_id.const_cpow (Or.inl h4dne)).mul
      (hP.differentiable_Λ s)).differentiableWithinAt
  · intro s hs
    have hmellin : mellin (fun u : ℝ => Work.FIArea5.S16Hecke.thetaHol psi 0 u) s
        = Complex.Gamma s * (Real.pi : ℂ) ^ (-s) *
            Work.FIArea5.S16Hecke.heckeLSeries psi 0 s := by
      have h := Work.FIArea5.S16Hecke.mellin_thetaHol psi 0 hb (s := s) (by simpa using hs)
      rw [mellin]
      have hswap : (fun x : ℝ => (x : ℂ) ^ (s - 1) • Work.FIArea5.S16Hecke.thetaHol psi 0 x)
          = fun x : ℝ => Work.FIArea5.S16Hecke.thetaHol psi 0 x * (x : ℂ) ^ (s - 1) := by
        funext x
        rw [smul_eq_mul, mul_comm]
      rw [hswap]
      simpa using h
    have hPΛ : P.Λ s = Complex.Gamma s * (Real.pi : ℂ) ^ (-s) *
        Work.FIArea5.S16Hecke.heckeLSeries psi 0 s := by
      rw [hΛeq, hmellin]
    change ((4 * (d : ℝ)) : ℂ) ^ s * P.Λ s
      = Work.FITop4.Bridge.heckeArch d 0 s * Work.FIArea5.S16Hecke.heckeLSeries psi 0 s
    rw [hPΛ, Work.FITop4.Bridge.heckeArch]
    have hgam : Complex.Gamma (s + ((|(((0 : ℤ) : ℝ))| / 2 : ℝ) : ℂ)) = Complex.Gamma s := by
      norm_num
    rw [hgam]
    have hbase : ((4 * (d : ℝ)) : ℂ) = (((4 * (d : ℝ) : ℝ)) : ℂ) := by
      push_cast; ring
    have hkey : (((4 * (d : ℝ) : ℝ) : ℂ) / (Real.pi : ℂ)) ^ s
        = (((4 * (d : ℝ) : ℝ) : ℂ)) ^ s * (Real.pi : ℂ) ^ (-s) := by
      rw [Complex.div_cpow_ofReal_nonneg (le_of_lt h4dpos) Real.pi_nonneg,
        Complex.cpow_neg, div_eq_mul_inv]
    rw [hbase, hkey]
    ring

/-! ## the target theorem -/

/-- **Existence of the completion.**  For a strict character `χ` mod `4d` which is *nontrivial on the
primary elements that are units modulo `4d`* (equivalently `χ` is not the principal strict character,
so that its Hecke `L`-function is entire, i.e. there is no pole at `s = 1`), there is an entire
function `Lam` agreeing with `heckeArch d 0 s · heckeLSeries χ 0 s` on the half-plane `re s > 1`.

Note the witness must be a *unit* mod `4d`: the principal strict character vanishes off the units, so
"χ z ≠ 1 for some primary z" is satisfied by it and would make the statement FALSE (its `L`-function
is `ζ_{ℚ(i)}` with finitely many Euler factors removed, which has a pole at `s = 1`).

This is Hecke's theory: the completion is the Mellin transform of the theta series, and its existence
is the content of `heckeFE_primitive_full` for primitive `χ`; for a general strict character one
conjugates by the (finite) product of Euler factors over the Gaussian primes dividing `4d` of a
character through whose modulus `χ` factors. -/
theorem exists_completion_strict {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hnontriv : ∃ z : GaussianInt,
      Work.FIPlan.IsPrimary z ∧ Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) :
    ∃ Lam : ℂ → ℂ, AnalyticOn ℂ Lam Set.univ ∧
      ∀ s : ℂ, 1 < s.re →
        Lam s = Work.FITop4.Bridge.heckeArch d 0 s * Work.FIArea5.S16Hecke.heckeLSeries chi 0 s := by
  have hpsi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d (Work.FIArea5.S16Hecke.twist chi 0) :=
    Work.FIArea5.S16Hecke.twist_isCharMod4dStrict d hd chi 0 hchi
  have hU : Work.FIArea5.S16Hecke.unitSum (Work.FIArea5.S16Hecke.twist chi 0) 0 ≠ 0 := by
    rw [Work.FIArea5.S16Hecke.twist_unitSum d hd chi 0 hchi.1]
    norm_num
  have h0 : Work.FIArea5.S16Hecke.gaussSum d (Work.FIArea5.S16Hecke.twist chi 0) 0 = 0 := by
    refine gaussSum_zero_of_nontrivial hd hpsi ?_
    obtain ⟨z, hz1, hz2, hz3⟩ := hnontriv
    exact ⟨z, hz1, hz2, by
      rw [Work.FIArea5.S16Hecke.twist_eq_of_isPrimary chi 0 hz1]; exact hz3⟩
  obtain ⟨Lam, hAn, hv⟩ := completion_of_unitSum_ne_zero hd hpsi hU h0
  refine ⟨Lam, hAn, fun s hs => ?_⟩
  have htw : Work.FIArea5.S16Hecke.heckeLSeries (Work.FIArea5.S16Hecke.twist chi 0) 0
      = Work.FIArea5.S16Hecke.heckeLSeries chi 0 := by
    simpa using Work.FIArea6Hecke.heckeLSeries_twist chi 0
  rw [hv s hs]
  exact congrArg (fun f : ℂ → ℂ => Work.FITop4.Bridge.heckeArch d 0 s * f s) htw

end

end Work.FIArea6Hecke.R
