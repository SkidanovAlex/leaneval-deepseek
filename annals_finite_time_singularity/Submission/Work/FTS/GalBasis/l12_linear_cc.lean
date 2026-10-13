/-
# `Work.FTS.GalBasis.l12_linear_cc` — linearity of the `L₁₂` zero mode on the test class

The zero mode of the fundamental model,

  `L₁₂(f)(z) = ∫_z^∞ ∫_0^{π/2} K(θ) f(s,θ)/s dθ ds`,   `K(θ) = 3 sin θ cos²θ`,

is an integral, hence additive and homogeneous in the profile `f`.  This file proves the three
linearity identities for the *test class* `Ccφ` of the Galerkin basis of this chapter
(`GalBasis/Defs.lean`): `f` is globally `C^∞` and supported strictly inside a box
`[a,b] × [δ,π/2-δ]` with `0 < a < b`, `0 < δ < π/2`.  That class is exactly what makes the
integrability side conditions of the two-layer integral harmless:

* the angular slice `θ ↦ K θ · f(s,θ)/s` is continuous on the compact `Iθ = [0,π/2]`
  (`slice_integrable_of_cc`), so the *density* `L₁₂dens` splits additively;
* the density is supported in the compact `z`-interval `[a',b'] ⊂ (0,∞)` and continuous there,
  hence integrable on `Ioi 0` (`dens_integrable_of_cc`), so the outer integral splits.

The finite-sum clause is the existing `Work.FTS.Apriori.ZeroMode.L12_sum_zero` (additivity over a
`Finset`, only needing the two families of integrability inputs), fed with the same two lemmas.

Everything here is stated for `Work.FTS.Galerkin.Fn = ℝ → ℝ → ℝ`, and the weight is
`Work.Spaces.K` (`K(θ) = 3 sin θ cos²θ`); the interval is `Work.Spaces.Iθ = [0,π/2]`, matching
the definitions of `Work.FM` and `Work.Construction`.

## Relation to the parallel deliveries

The two integrability facts above were *also* proved, in parallel with this file, by colleagues,
as the standalone lemmas

* `Work.FTS.GalBasis.cc_slice_integrable` (`GalBasis/cc_slice_integrable.lean`),
* `Work.FTS.GalBasis.cc_dens_integrable` (`GalBasis/cc_dens_integrable.lean`, via the
  `ℋ⁴`-integrability `Work.FTS.H2.L12densIntegrable` and `Work.FTS.GalBasis.cc_mem_all`);

either route supplies the inputs of the assembly below.  This file reproves them directly (a
compact-support argument: continuity on the compact `θ`-interval, support in a compact
`z`-interval `⊂ (0,∞)`, then transport of `IntegrableOn` from `Icc a' b'` to `Ioi 0`), which
keeps the import cone of `l12_linear_cc` to `FM` / `LocData` / `Apriori.ZeroMode` and free of the
much heavier `H2`-`Coercivity` machinery.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.GalBasis.Defs
import Submission.Work.FTS.Apriori.ZeroMode.L12_sum_zero
import Submission.Work.FTS.LocData.L12_add_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

open Work.FTS.Galerkin (Fn galFun)

set_option autoImplicit false
set_option maxHeartbeats 400000

/-! ## Integrability of the slice and of the density of a `Ccφ` test function -/

/-- **Slice integrability.**  For a `Ccφ` function `F` the angular slice
`θ ↦ K(θ)·(c·F z θ)/z` is continuous on the compact `Iθ = [0,π/2]`, hence integrable there.
(The hypothesis `0 < z` is not actually used: division by the constant `z` is continuous even
at `z = 0`; it is kept for compatibility with the consumers.) -/
theorem slice_integrable_of_cc {F : Fn} (h : Ccφ F) (c : ℝ) :
    ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * (c * F z θ) / z) Work.Spaces.Iθ := by
  intro z _
  have hu : Continuous (Function.uncurry F) := h.contDiff.continuous
  have hFz : Continuous (fun θ : ℝ => F z θ) :=
    hu.comp ((continuous_const : Continuous (fun _ : ℝ => z)).prodMk continuous_id)
  have hK : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
    unfold Work.Spaces.K
    fun_prop
  have hc : Continuous (fun θ : ℝ => Work.Spaces.K θ * (c * F z θ) / z) :=
    (hK.mul ((continuous_const : Continuous (fun _ : ℝ => c)).mul hFz)).div_const z
  exact hc.continuousOn.integrableOn_compact isCompact_Icc

/-- **Density integrability, general form.**  If `G` is continuous and vanishes whenever
`z ∉ [a,b]` with `0 < a`, then its angular density `s ↦ L₁₂dens K G s` is supported in the
compact interval `[a,b] ⊂ (0,∞)` and is continuous there (it is `(∫_θ K θ · G s θ)/s`, a
parametric integral with a continuous integrand), hence integrable on `Ioi 0`. -/
theorem dens_integrable_of_cont_supp {G : ℝ → ℝ → ℝ} {a b : ℝ}
    (hcont : Continuous (Function.uncurry G))
    (hsupp : ∀ z θ, z ∉ Set.Icc a b → G z θ = 0) (ha : 0 < a) :
    MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K G s) (Set.Ioi 0) := by
  have hK : Continuous (fun θ : ℝ => Work.Spaces.K θ) := by
    unfold Work.Spaces.K
    fun_prop
  -- the density vanishes off the `z`-support of `G`
  have hsupp' : ∀ s : ℝ, s ∉ Set.Icc a b → Work.FM.L12dens Work.Spaces.K G s = 0 := by
    intro s hs
    rw [Work.FM.L12dens]
    have hzero : (fun θ => Work.Spaces.K θ * G s θ / s) = fun _ => (0 : ℝ) := by
      funext θ
      rw [hsupp s θ hs]
      ring
    rw [hzero]
    simp
  -- the parametric integral `s ↦ ∫_θ K θ · G s θ` is continuous
  have hI : Continuous (fun s : ℝ => ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G s θ) := by
    refine continuous_parametric_integral_of_continuous ?_ ?_
    · exact (hK.comp continuous_snd).mul hcont
    · simpa only [Work.Spaces.Iθ] using isCompact_Icc
  have hne : ∀ s ∈ Set.Icc a b, s ≠ 0 := fun s hs => ne_of_gt (lt_of_lt_of_le ha hs.1)
  have hdiv : ContinuousOn
      (fun s : ℝ => (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G s θ) / s) (Set.Icc a b) :=
    hI.continuousOn.div continuousOn_id hne
  have hEqOn : Set.EqOn (fun s => Work.FM.L12dens Work.Spaces.K G s)
      (fun s : ℝ => (∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ * G s θ) / s) (Set.Icc a b) :=
    fun s hs => Work.FM.L12dens_eq (K := Work.Spaces.K) (f := G) (hne s hs)
  have hcontOn : ContinuousOn (fun s => Work.FM.L12dens Work.Spaces.K G s) (Set.Icc a b) :=
    hdiv.congr hEqOn
  have hInt : MeasureTheory.IntegrableOn (fun s => Work.FM.L12dens Work.Spaces.K G s)
      (Set.Icc a b) := hcontOn.integrableOn_compact isCompact_Icc
  -- transport from the compact interval to `Ioi 0`
  have hset : Set.Icc a b ∩ Set.Ioi (0 : ℝ) = Set.Icc a b :=
    Set.inter_eq_left.mpr (fun s hs => lt_of_lt_of_le ha hs.1)
  have hind : MeasureTheory.IntegrableOn
      ((Set.Icc a b).indicator (fun s => Work.FM.L12dens Work.Spaces.K G s)) (Set.Ioi 0) := by
    rw [MeasureTheory.integrableOn_indicator_iff measurableSet_Icc, hset]
    exact hInt
  have heq : Set.EqOn ((Set.Icc a b).indicator (fun s => Work.FM.L12dens Work.Spaces.K G s))
      (fun s => Work.FM.L12dens Work.Spaces.K G s) (Set.Ioi 0) := by
    intro s _
    by_cases hm : s ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm]
      exact (hsupp' s hm).symm
  exact (MeasureTheory.integrableOn_congr_fun heq measurableSet_Ioi).mp hind

/-- **Density integrability for the test class.**  The density of any scalar multiple of a
`Ccφ` function is integrable on `Ioi 0`. -/
theorem dens_integrable_of_cc {F : Fn} (h : Ccφ F) (c : ℝ) :
    MeasureTheory.IntegrableOn
      (fun z => Work.FM.L12dens Work.Spaces.K (fun z θ => c * F z θ) z) (Set.Ioi 0) := by
  obtain ⟨a, b, δ, ha, hab, hδ, hδ2, hd, a', b', δ', haa, hab', hbb, hδδ, hδδ2, hs⟩ := h
  refine dens_integrable_of_cont_supp (G := fun z θ => c * F z θ) (a := a') (b := b') ?_ ?_
    (lt_trans ha haa)
  · exact (continuous_const : Continuous (fun _ : ℝ × ℝ => c)).mul hd.continuous
  · intro z θ hz
    rw [hs z θ (Or.inl hz), mul_zero]

/-! ## The linearity identities -/

theorem l12_linear_cc :
    (∀ f g : Work.FTS.Galerkin.Fn, Ccφ f → Ccφ g →
      Work.Construction.L12 (fun z θ => f z θ + g z θ) 0
        = Work.Construction.L12 f 0 + Work.Construction.L12 g 0) ∧
    (∀ (c : ℝ) (f : Work.FTS.Galerkin.Fn), Ccφ f →
      Work.Construction.L12 (fun z θ => c * f z θ) 0 = c * Work.Construction.L12 f 0) ∧
    (∀ (n : ℕ) (φ : ℕ → Work.FTS.Galerkin.Fn), (∀ k : Fin n, Ccφ (φ k)) → ∀ c : Fin n → ℝ,
      Work.Construction.L12 (Work.FTS.Galerkin.galFun φ c) 0
        = ∑ k : Fin n, c k * Work.Construction.L12 (φ (k : ℕ)) 0) := by
  -- the unscaled slice and density integrability of a `Ccφ` function
  have hslice : ∀ (F : Fn), Ccφ F → ∀ s ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ * F s θ / s) Work.Spaces.Iθ := by
    intro F hF s hs
    have h1 := slice_integrable_of_cc hF 1 s hs
    refine h1.congr_fun (fun θ _ => ?_) (by simpa only [Work.Spaces.Iθ] using measurableSet_Icc)
    ring
  have hdens : ∀ (F : Fn), Ccφ F →
      MeasureTheory.IntegrableOn (fun z => Work.FM.L12dens Work.Spaces.K F z) (Set.Ioi 0) := by
    intro F hF
    have h1 := dens_integrable_of_cc hF 1
    refine (MeasureTheory.integrableOn_congr_fun (f := fun z => Work.FM.L12dens Work.Spaces.K
      (fun z θ => (1 : ℝ) * F z θ) z) (g := fun z => Work.FM.L12dens Work.Spaces.K F z)
      ?_ measurableSet_Ioi).mp h1
    intro z _
    show Work.FM.L12dens Work.Spaces.K (fun z θ => (1 : ℝ) * F z θ) z
        = Work.FM.L12dens Work.Spaces.K F z
    rw [Work.FTS.LocData.L12dens_const_mul, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · -- additivity
    intro f g hf hg
    show Work.FM.L12 Work.Spaces.K (fun z θ => f z θ + g z θ) 0
        = Work.FM.L12 Work.Spaces.K f 0 + Work.FM.L12 Work.Spaces.K g 0
    simp only [Work.FM.L12]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun s hs => Work.FTS.LocData.L12dens_add_of_integrableOn Work.Spaces.K
        (hslice f hf s hs) (hslice g hg s hs))]
    exact MeasureTheory.integral_add (hdens f hf) (hdens g hg)
  · -- homogeneity
    intro c f hf
    show Work.FM.L12 Work.Spaces.K (fun z θ => c * f z θ) 0
        = c * Work.FM.L12 Work.Spaces.K f 0
    exact Work.FM.L12_const_mul
  · -- finite sums
    intro n φ hφ c
    have htheta : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
          (fun θ => Work.Spaces.K θ * (c k * φ (k : ℕ) z θ) / z) Work.Spaces.Iθ :=
      fun k _ z hz => slice_integrable_of_cc (hφ k) (c k) z hz
    have hdens' : ∀ k ∈ (Finset.univ : Finset (Fin n)),
        MeasureTheory.IntegrableOn
          (fun z => Work.Construction.L12dens (fun z θ => c k * φ (k : ℕ) z θ) z) (Set.Ioi 0) :=
      fun k _ => by
        simpa only [Work.Construction.L12dens] using dens_integrable_of_cc (hφ k) (c k)
    have key := Work.FTS.Apriori.ZeroMode.L12_sum_zero (Finset.univ : Finset (Fin n))
      (fun k : Fin n => fun z θ => c k * φ (k : ℕ) z θ) htheta hdens'
    have hlhs : Work.Construction.L12 (Work.FTS.Galerkin.galFun φ c) 0
        = Work.Construction.L12 (fun z θ => ∑ k : Fin n, c k * φ (k : ℕ) z θ) 0 := rfl
    rw [hlhs, key]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    show Work.FM.L12 Work.Spaces.K (fun z θ => c k * φ (k : ℕ) z θ) 0
        = c k * Work.FM.L12 Work.Spaces.K (φ (k : ℕ)) 0
    exact Work.FM.L12_const_mul

end Work.FTS.GalBasis
