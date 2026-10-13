/-
# `StrongEps/IsEpsSolP_eq_of_epsClass_proof.lean` — **D1**: fixed-ε uniqueness of the scheme

(curric-46 lead install 2026-10-11; `cbc/fts_strongeps_c1c5_ruling.md` §5 step 2.)

Statement: two solutions `g`, `g'` of the projected `ε`-scheme at the *same* `ε`, with the
*same* datum `g₀`, whose slices lie in the engine's class `EpsEngine.EpsClass α ρ ε C₁ B` on
`[0,T]` and are jointly `C¹` on the strip, agree pointwise on the open quadrant, for every
`τ ∈ [0,T]`.

Route.
* `IsEpsSolP` only sees a family through its slices, and the scheme's right-hand side only through
  the *projected mollified* profile (`EpsEngine.epsRHSP_eq_Feps_slice`): writing
  `F := EpsEngine.Feps α ρ ε Φs E`, both families satisfy the Volterra equation
  `w τ = ∫₀^τ (F (slice g s) - F (slice g' s)) ds` pointwise on the quadrant
  (`Work.FTS.StrongEps.IsEpsSolPQ.epsSolP_volterra`, from `IsEpsSolP` plus the joint `C¹`; the
  joint `C¹` is what makes the fake-time integrand continuous at each fixed `(z,θ)`, hence
  interval-integrable, which the fundamental theorem of calculus needs);
* Cauchy–Schwarz in the fake time and Tonelli turn this into the `L²`-Minkowski estimate
  `√(EpsSq α (w τ)) ≤ ∫₀^τ √(EpsSq α (G s)) ds` (`…IsEpsSolPQ.EpsSq_intervalIntegral_le_sqrt`);
* the proved gate `EpsEngine.BddLip_of_epsClass` (through `EpsRHSPLipX`/`ConjTwo`) is a Lipschitz
  bound in the weighted space `X = (EpsMem, EpsSq)` on the class `EpsClass`, giving
  `EpsSq α (G s) ≤ L · EpsSq α (w s)` for every `s ∈ [0,T]`;
* the integral inequality `φ(τ) ≤ √L ∫₀^τ φ(s) ds` for `φ(τ) := √(EpsSq α (w τ))` is then
  iterated (`…IsEpsSolPQ.eq_zero_of_le_mul_intervalIntegral`), giving `EpsSq α (w τ) = 0`;
* `EpsSq α (w τ) = 0` with the honesty `EpsMem α (w τ)` says the weighted profile vanishes a.e.
  on the quadrant, and `w τ` is continuous there (`SmoothOpen` of both slices), so `w τ = 0` on
  the quadrant.

The honesty inputs (`EpsMem`) are produced by `EpsLocalPStar.EpsMemOfClassCJeps`: the `ClassC`
clause of `EpsClass` — which is a clause about the *projected mollified* slice `Pz (J_ε (slice g τ))`
— forces the raw slice `slice g τ` (and hence the difference) to be an honest member of the
weighted space.  Without that, `EpsSq` (a Bochner integral) would be Lean's junk value `0` on the
differences and the Grönwall estimate would be vacuous.

The statement is the requested one verbatim; the file opens `scoped Real` because the `π` of the
statement is `Real.pi` (this workspace's imports set `autoImplicit false`, so a bare `π` would
otherwise be an unknown identifier).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.EpsEngine.EpsSq_intervalIntegral_le_gen
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.EpsEngine.VolterraV4Main
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps
import Submission.Work.FTS.StrongEps.EpsSqTools.L12_zero_le_EpsSq
import Submission.Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_intervalIntegral_le_sqrt
import Submission.Work.FTS.StrongEps.IsEpsSolPQ.eq_zero_of_le_mul_intervalIntegral
import Submission.Work.FTS.StrongEps.IsEpsSolPQ.epsSolP_volterra

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps.IsEpsSolPQ

set_option autoImplicit false

/-! ## Elementary honesty facts -/

/-- `EpsSq` is the integral of the weighted square over the domain measure `DomM`, for honest
members of the weighted space. -/
theorem EpsSq_eq_integral_DomM {α : ℝ} {f : Fn} (hf : EpsMem α f) :
    (∫ p : ℝ × ℝ, (f p.1 p.2 * epsW α p.1 p.2) ^ 2 ∂EpsLocalPStar.DomM) = EpsSq α f := by
  have hg : Integrable (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2)
      EpsLocalPStar.DomM := (EpsLocalPStar.EpsMem_iff_integrable2).mp hf
  rw [EpsSq, EpsLocalPStar.DomM]
  exact MeasureTheory.integral_prod _ hg

/-- A member of the engine's class `EpsClass` is an honest member of the weighted space: this is
`EpsMemOfClassCJeps`, whose hypothesis is exactly the `ClassC` clause of `EpsClass` (a statement
about the *projected mollified* slice). -/
theorem EpsMem_of_EpsClass {α C₁ B ε : ℝ} {ρ : ℝ × ℝ → ℝ} {u : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B u) : EpsMem α u := by
  obtain ⟨C, hC, h⟩ := Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps ρ hρ
  exact (h α hα ε hε hε1 u hu.smoothOpen hu.hkMem hu.classC).1

/-- `EpsSq α u` is bounded by the `ℋ¹`-size of `u` for the slices of the engine's class (the
bound itself is the second conjunct of `EpsMemOfClassCJeps`). -/
theorem EpsSq_of_EpsClass_le {α C₁ B ε : ℝ} {ρ : ℝ × ℝ → ℝ} {u : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B u) :
    ∃ C : ℝ, 0 < C ∧ EpsSq α u ≤ C / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 u := by
  obtain ⟨C, hC, h⟩ := Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps ρ hρ
  exact ⟨C, hC, (h α hα ε hε hε1 u hu.smoothOpen hu.hkMem hu.classC).2⟩

/-- A `SmoothOpen` profile is a.e. strongly measurable in the weighted sense. -/
theorem AK2_of_SmoothOpen {α : ℝ} {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u) :
    EpsLocalPStar.AK2 α u := by
  rw [EpsLocalPStar.AK2]
  have hc : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (hu.forall 0).continuousOn
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => u p.1 p.2)
      EpsLocalPStar.DomM := by
    simpa only [EpsLocalPStar.DomM] using Work.Spaces.aesm_of_continuousOn_Qd _ hc
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => epsW α p.1 p.2) EpsLocalPStar.DomM :=
    (EpsLocalPStar.measurable_epsW α).aestronglyMeasurable
  refine (h1.mul h2).congr ?_
  filter_upwards with p
  simp only [Pi.mul_apply]

/-- The difference of two admissible slices is an honest member of the weighted space. -/
theorem EpsMem_sub_of_EpsClass {α C₁ B ε : ℝ} {ρ : ℝ × ℝ → ℝ} {u v : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B u)
    (hv : Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B v) :
    EpsMem α (fun z θ => u z θ - v z θ) :=
  EpsLocalPStar.EpsMem_sub2 (AK2_of_SmoothOpen hu.smoothOpen) (AK2_of_SmoothOpen hv.smoothOpen)
    (EpsMem_of_EpsClass hα hρ hε hε1 hu) (EpsMem_of_EpsClass hα hρ hε hε1 hv)

/-- Pointwise domination of the weighted square of a difference (used to transfer integrability
and to bound `EpsSq` of a difference in terms of the two `EpsSq`'s). -/
theorem sq_sub_mul_le {a b c : ℝ} :
    ((a - b) * c) ^ 2 ≤ 2 * (a * c) ^ 2 + 2 * (b * c) ^ 2 := by
  nlinarith [sq_nonneg (a * c), sq_nonneg (b * c), sq_nonneg (a * c + b * c),
    sq_nonneg (a * c - b * c)]

/-- `EpsSq` of a difference is controlled by the two `EpsSq`'s, for honest summands. -/
theorem EpsSq_sub_le {α : ℝ} {u v : Fn} (hu : EpsMem α u) (hv : EpsMem α v)
    (huv : EpsMem α (fun z θ => u z θ - v z θ)) :
    EpsSq α (fun z θ => u z θ - v z θ) ≤ 2 * EpsSq α u + 2 * EpsSq α v := by
  have hX : Integrable (fun p : ℝ × ℝ => (u p.1 p.2 * epsW α p.1 p.2) ^ 2)
      EpsLocalPStar.DomM := (EpsLocalPStar.EpsMem_iff_integrable2).mp hu
  have hY : Integrable (fun p : ℝ × ℝ => (v p.1 p.2 * epsW α p.1 p.2) ^ 2)
      EpsLocalPStar.DomM := (EpsLocalPStar.EpsMem_iff_integrable2).mp hv
  have hD : Integrable
      (fun p : ℝ × ℝ => ((u p.1 p.2 - v p.1 p.2) * epsW α p.1 p.2) ^ 2)
      EpsLocalPStar.DomM := (EpsLocalPStar.EpsMem_iff_integrable2).mp huv
  rw [← EpsSq_eq_integral_DomM huv, ← EpsSq_eq_integral_DomM hu, ← EpsSq_eq_integral_DomM hv]
  refine le_trans (MeasureTheory.integral_mono hD (hX.const_mul 2 |>.add (hY.const_mul 2))
    (fun p => sq_sub_mul_le)) ?_
  simp only [Pi.add_apply]
  rw [MeasureTheory.integral_add (hX.const_mul 2) (hY.const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- **Measurability of the `√EpsSq` of a jointly measurable, a.e. honest curve of profiles.**
Together with an a.e. bound this is the integrability input of the Minkowski/Grönwall step. -/
theorem aesm_sqrt_EpsSq {α τ : ℝ} {Φ : ℝ → Fn}
    (hmeas : AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => Φ q.1 q.2.1 q.2.2 * epsW α q.2.1 q.2.2)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod EpsLocalPStar.DomM))
    (hmem : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)), EpsMem α (Φ s)) :
    AEStronglyMeasurable (fun s : ℝ => Real.sqrt (EpsSq α (Φ s)))
      (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) := by
  have h1 : AEStronglyMeasurable
      (fun s : ℝ => ∫ p : ℝ × ℝ,
        (Φ s p.1 p.2 * epsW α p.1 p.2) ^ 2 ∂EpsLocalPStar.DomM)
      (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) :=
    (hmeas.pow 2).integral_prod_right'
  refine (Real.continuous_sqrt.comp_aestronglyMeasurable h1).congr ?_
  filter_upwards [hmem] with s hs
  rw [EpsSq_eq_integral_DomM hs]

end Work.FTS.StrongEps.IsEpsSolPQ

namespace Work.FTS.StrongEps

set_option autoImplicit false

theorem IsEpsSolP_eq_of_epsClass_proof {α C₁ Ce Cs B T ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {g g' : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hT : 0 < T)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E)
    (hB : 0 ≤ B)
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hsol' : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g')
    (hcl : ∀ τ ∈ Set.Icc 0 T, Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B
      (Work.FTS.Galerkin.slice g τ))
    (hcl' : ∀ τ ∈ Set.Icc 0 T, Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B
      (Work.FTS.Galerkin.slice g' τ))
    (hc1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    (hc1' : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g' p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T)) :
    ∀ τ ∈ Set.Icc 0 T, ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → g z θ τ = g' z θ τ := by
  -- ## abbreviations of the argument
  set F : Fn → Fn := Work.FTS.EpsEngine.Feps α ρ ε Φs E with hFdef
  set W : ℝ → Fn := fun s z θ =>
    Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g' s z θ with hWdef
  set Gc : ℝ → Fn := fun s z θ =>
    F (Work.FTS.Galerkin.slice g s) z θ - F (Work.FTS.Galerkin.slice g' s) z θ with hGcdef
  have hT0 : 0 ≤ T := hT.le
  -- ## the Lipschitz gate of the engine at the radius of the class
  obtain ⟨L, hLpos, hbd, hlip⟩ := Work.FTS.EpsEngine.BddLip_of_epsClass
    (α := α) (C₁ := C₁) (Ce := Ce) (Cs := Cs) (B := B) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε)
    hα hρ hε hε1 hEll hstar hml hB
  have hL0 : 0 ≤ L := hLpos.le
  -- ## the Volterra identity, together with the joint measurability of the two curves
  obtain ⟨hvol, hmeasG, hmeasW⟩ := Work.FTS.StrongEps.IsEpsSolPQ.epsSolP_volterra
    (α := α) (C₁ := C₁) (Ce := Ce) (Cs := Cs) (B := B) (T := T) (ε := ε) (ρ := ρ) (Φs := Φs)
    (E := E) (g₀ := g₀) (g := g) (g' := g') hα hρ hε hε1 hT hEll hstar hml hB hsol hsol' hc1 hc1'
  -- ## honesty of the slices and of their difference
  have hmem_slice : ∀ τ ∈ Set.Icc 0 T, EpsMem α (Work.FTS.Galerkin.slice g τ) := fun τ hτ =>
    Work.FTS.StrongEps.IsEpsSolPQ.EpsMem_of_EpsClass hα hρ hε hε1 (hcl τ hτ)
  have hmem_slice' : ∀ τ ∈ Set.Icc 0 T, EpsMem α (Work.FTS.Galerkin.slice g' τ) := fun τ hτ =>
    Work.FTS.StrongEps.IsEpsSolPQ.EpsMem_of_EpsClass hα hρ hε hε1 (hcl' τ hτ)
  have hmemW : ∀ τ ∈ Set.Icc 0 T, EpsMem α (W τ) := fun τ hτ =>
    Work.FTS.StrongEps.IsEpsSolPQ.EpsMem_sub_of_EpsClass hα hρ hε hε1 (hcl τ hτ) (hcl' τ hτ)
  -- ## the two halves of the right-hand side are honest and bounded
  have hmemF : ∀ τ ∈ Set.Icc 0 T, EpsMem α (F (Work.FTS.Galerkin.slice g τ)) := fun τ hτ =>
    (hbd _ (hcl τ hτ)).1
  have hmemF' : ∀ τ ∈ Set.Icc 0 T, EpsMem α (F (Work.FTS.Galerkin.slice g' τ)) := fun τ hτ =>
    (hbd _ (hcl' τ hτ)).1
  have hbdF : ∀ τ ∈ Set.Icc 0 T, EpsSq α (F (Work.FTS.Galerkin.slice g τ)) ≤ L := fun τ hτ =>
    (hbd _ (hcl τ hτ)).2
  have hbdF' : ∀ τ ∈ Set.Icc 0 T, EpsSq α (F (Work.FTS.Galerkin.slice g' τ)) ≤ L := fun τ hτ =>
    (hbd _ (hcl' τ hτ)).2
  -- ## a.e. honesty and a.e. boundedness of the right-hand side curve
  have hsae : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 T)), s ∈ Set.Icc 0 T := by
    have h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 T)), s ∈ Set.Ioc 0 T := by
      rw [Set.uIoc_of_le hT0]
      exact MeasureTheory.ae_restrict_mem measurableSet_Ioc
    filter_upwards [h1] with s hs using ⟨hs.1.le, hs.2⟩
  have hAKG : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 T)),
      Work.FTS.StrongEps.EpsLocalPStar.AK2 α (Gc s) := by
    have h1 := (hmeasG T ⟨hT0, le_refl T⟩).prodMk_left
    filter_upwards [h1] with s hs using hs
  have hmemG : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 T)), EpsMem α (Gc s) := by
    filter_upwards [hAKG, hsae] with s hsAK hsI
    rw [Work.FTS.StrongEps.EpsLocalPStar.EpsMem_iff_integrable2]
    have hmeas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (Gc s p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        Work.FTS.StrongEps.EpsLocalPStar.DomM := hsAK.pow 2
    have hXu : Integrable (fun p : ℝ × ℝ => (F (Work.FTS.Galerkin.slice g s) p.1 p.2
        * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) Work.FTS.StrongEps.EpsLocalPStar.DomM :=
      (Work.FTS.StrongEps.EpsLocalPStar.EpsMem_iff_integrable2).mp (hmemF s hsI)
    have hXv : Integrable (fun p : ℝ × ℝ => (F (Work.FTS.Galerkin.slice g' s) p.1 p.2
        * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) Work.FTS.StrongEps.EpsLocalPStar.DomM :=
      (Work.FTS.StrongEps.EpsLocalPStar.EpsMem_iff_integrable2).mp (hmemF' s hsI)
    have hdom : Integrable (fun p : ℝ × ℝ => 2 * (F (Work.FTS.Galerkin.slice g s) p.1 p.2
          * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
        + 2 * (F (Work.FTS.Galerkin.slice g' s) p.1 p.2
          * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) Work.FTS.StrongEps.EpsLocalPStar.DomM :=
      (hXu.const_mul 2).add (hXv.const_mul 2)
    refine Integrable.mono' hdom hmeas ?_
    filter_upwards with p
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := Work.FTS.StrongEps.IsEpsSolPQ.sq_sub_mul_le
      (a := F (Work.FTS.Galerkin.slice g s) p.1 p.2)
      (b := F (Work.FTS.Galerkin.slice g' s) p.1 p.2)
      (c := Work.FTS.StrongEps.epsW α p.1 p.2)
    simpa only [hGcdef] using h
  have hbndG : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 T)), EpsSq α (Gc s) ≤ 4 * L := by
    filter_upwards [hmemG, hsae] with s hmem hsI
    have hsub := Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_sub_le (hmemF s hsI) (hmemF' s hsI) hmem
    have h1 := hbdF s hsI
    have h2 := hbdF' s hsI
    have hsub' : EpsSq α (Gc s) ≤ 2 * EpsSq α (F (Work.FTS.Galerkin.slice g s))
        + 2 * EpsSq α (F (Work.FTS.Galerkin.slice g' s)) := by
      simpa only [hGcdef] using hsub
    linarith
  -- ## the Lipschitz bound in the strong weight
  have hlipW : ∀ τ ∈ Set.Icc 0 T, EpsSq α (Gc τ) ≤ L * EpsSq α (W τ) := by
    intro τ hτ
    have h := hlip (Work.FTS.Galerkin.slice g τ) (Work.FTS.Galerkin.slice g' τ)
      (hcl τ hτ) (hcl' τ hτ)
    simpa only [hGcdef, hWdef, hFdef] using h
  -- ## the `L²`-Minkowski estimate, for every horizon
  have hMink : ∀ τ ∈ Set.Icc 0 T,
      EpsSq α (W τ) ≤ (∫ s in (0 : ℝ)..τ, Real.sqrt (EpsSq α (Gc s))) ^ 2 := by
    intro τ hτ
    have hsubu : Set.uIoc 0 τ ⊆ Set.uIoc 0 T := by
      rw [Set.uIoc_of_le hτ.1, Set.uIoc_of_le hT0]
      exact Set.Ioc_subset_Ioc_right hτ.2
    have hle : MeasureTheory.volume.restrict (Set.uIoc 0 τ)
        ≤ MeasureTheory.volume.restrict (Set.uIoc 0 T) :=
      MeasureTheory.Measure.restrict_mono hsubu (le_refl _)
    have hGmem' : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)), EpsMem α (Gc s) :=
      Filter.Eventually.filter_mono (MeasureTheory.ae_mono hle) hmemG
    have hbnd' : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)), EpsSq α (Gc s) ≤ 4 * L :=
      Filter.Eventually.filter_mono (MeasureTheory.ae_mono hle) hbndG
    have hw : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
        W τ p.1 p.2 = ∫ s in (0 : ℝ)..τ, Gc s p.1 p.2 := by
      filter_upwards [Work.FTS.StrongEps.EpsLocalPStar.ae_open_DomM] with p hp
      have h := hvol p.1 p.2 τ hp.1 ⟨hp.2.1, hp.2.2⟩ hτ
      simpa only [hWdef, hGcdef, hFdef, Work.FTS.Galerkin.slice] using h
    exact Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_intervalIntegral_le_sqrt hτ.1 (by linarith)
      (hmeasG τ hτ) hGmem' hbnd' (hmemW τ hτ) hw
  -- ## the uniform bound on `φ = √(EpsSq α (W ·))`
  obtain ⟨CB, hCBpos, hCB⟩ := Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps ρ hρ
  set M : ℝ := Real.sqrt (4 * (CB / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2)) with hMdef
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hEpsSq_slice : ∀ τ ∈ Set.Icc 0 T,
      EpsSq α (Work.FTS.Galerkin.slice g τ) ≤ CB / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2 := by
    intro τ hτ
    have hb := (hCB α hα ε hε hε1 (Work.FTS.Galerkin.slice g τ) (hcl τ hτ).smoothOpen
      (hcl τ hτ).hkMem (hcl τ hτ).classC).2
    have hmono := Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (k := 1) (l := 6) (by norm_num)
      (hcl τ hτ).hkMem
    have hB2 : Work.Spaces.HkSq α 1 (Work.FTS.Galerkin.slice g τ) ≤ B ^ 2 := by
      refine le_trans hmono ?_
      rw [show Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)
        = (Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g τ)) ^ 2 from
          (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 _)).symm]
      exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) (hcl τ hτ).hkNorm 2
    exact le_trans hb (mul_le_mul_of_nonneg_left hB2 (div_nonneg hCBpos.le (sq_nonneg _)))
  have hEpsSq_slice' : ∀ τ ∈ Set.Icc 0 T,
      EpsSq α (Work.FTS.Galerkin.slice g' τ) ≤ CB / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2 := by
    intro τ hτ
    have hb := (hCB α hα ε hε hε1 (Work.FTS.Galerkin.slice g' τ) (hcl' τ hτ).smoothOpen
      (hcl' τ hτ).hkMem (hcl' τ hτ).classC).2
    have hmono := Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (k := 1) (l := 6) (by norm_num)
      (hcl' τ hτ).hkMem
    have hB2 : Work.Spaces.HkSq α 1 (Work.FTS.Galerkin.slice g' τ) ≤ B ^ 2 := by
      refine le_trans hmono ?_
      rw [show Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g' τ)
        = (Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g' τ)) ^ 2 from
          (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 _)).symm]
      exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) (hcl' τ hτ).hkNorm 2
    exact le_trans hb (mul_le_mul_of_nonneg_left hB2 (div_nonneg hCBpos.le (sq_nonneg _)))
  have hWbd : ∀ τ ∈ Set.Icc 0 T, EpsSq α (W τ) ≤ M ^ 2 := by
    intro τ hτ
    have hsub := Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_sub_le (hmem_slice τ hτ) (hmem_slice' τ hτ)
      (hmemW τ hτ)
    have hsub' : EpsSq α (W τ) ≤ 2 * EpsSq α (Work.FTS.Galerkin.slice g τ)
        + 2 * EpsSq α (Work.FTS.Galerkin.slice g' τ) := by
      simpa only [hWdef] using hsub
    have h1 := hEpsSq_slice τ hτ
    have h2 := hEpsSq_slice' τ hτ
    rw [hMdef, Real.sq_sqrt (by positivity)]
    linarith
  -- ## the Grönwall inequality
  have hmeasW2 : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => EpsSq α (W s))
      (MeasureTheory.volume.restrict (Set.uIoc 0 T)) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => ∫ p : ℝ × ℝ,
          (W s p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
          ∂Work.FTS.StrongEps.EpsLocalPStar.DomM)
        (MeasureTheory.volume.restrict (Set.uIoc 0 T)) :=
      ((hmeasW T ⟨hT0, le_refl T⟩).pow 2).integral_prod_right'
    refine h1.congr ?_
    filter_upwards [hsae] with s hsI
    exact Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_eq_integral_DomM (hmemW s hsI)
  have hφaeT : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Real.sqrt (EpsSq α (W s)))
      (MeasureTheory.volume.restrict (Set.uIoc 0 T)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hmeasW2
  have hbdaT : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 T)),
      ‖Real.sqrt (EpsSq α (W s))‖ ≤ M := by
    filter_upwards [hsae] with s hsI
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (EpsSq α (W s)) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt (hWbd s hsI)
      _ = M := Real.sqrt_sq hM0
  haveI hfinT : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc 0 T)) := ⟨by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_uIoc, sub_zero, abs_of_nonneg hT0]
    exact ENNReal.ofReal_lt_top⟩
  have hintφ : MeasureTheory.IntegrableOn (fun s : ℝ => Real.sqrt (EpsSq α (W s)))
      (Set.Icc 0 T) := by
    have hInt := MeasureTheory.Integrable.of_bound hφaeT M hbdaT
    show Integrable (fun s : ℝ => Real.sqrt (EpsSq α (W s)))
      (MeasureTheory.volume.restrict (Set.Icc 0 T))
    rw [← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := T)),
      ← Set.uIoc_of_le hT0]
    exact hInt
  have hgron : ∀ τ ∈ Set.Icc 0 T, Real.sqrt (EpsSq α (W τ)) = 0 := by
    refine Work.FTS.StrongEps.IsEpsSolPQ.eq_zero_of_le_mul_intervalIntegral
      (Real.sqrt_nonneg L) hT0 hM0 hintφ (fun τ hτ => Real.sqrt_nonneg _)
      (fun τ hτ => ?_) (fun τ hτ => ?_)
    · calc Real.sqrt (EpsSq α (W τ)) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt (hWbd τ hτ)
        _ = M := Real.sqrt_sq hM0
    · have hsubu : Set.uIoc 0 τ ⊆ Set.uIoc 0 T := by
        rw [Set.uIoc_of_le hτ.1, Set.uIoc_of_le hT0]
        exact Set.Ioc_subset_Ioc_right hτ.2
      have hle : MeasureTheory.volume.restrict (Set.uIoc 0 τ)
          ≤ MeasureTheory.volume.restrict (Set.uIoc 0 T) :=
        MeasureTheory.Measure.restrict_mono hsubu (le_refl _)
      -- interval integrability of the three curves
      have hφint : IntervalIntegrable (fun s : ℝ => Real.sqrt (EpsSq α (W s)))
          MeasureTheory.volume 0 τ := by
        have hφae : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Real.sqrt (EpsSq α (W s)))
            (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) :=
          Real.continuous_sqrt.comp_aestronglyMeasurable (hmeasW2.mono_measure hle)
        have hbd : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)),
            ‖Real.sqrt (EpsSq α (W s))‖ ≤ M :=
          Filter.Eventually.filter_mono (MeasureTheory.ae_mono hle) hbdaT
        exact IntervalIntegrable.mono_fun'
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) MeasureTheory.volume 0 τ)
          hφae hbd
      have hLint : IntervalIntegrable (fun s : ℝ => Real.sqrt L * Real.sqrt (EpsSq α (W s)))
          MeasureTheory.volume 0 τ := hφint.const_mul (Real.sqrt L)
      have hGae : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Real.sqrt (EpsSq α (Gc s)))
          (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) :=
        Work.FTS.StrongEps.IsEpsSolPQ.aesm_sqrt_EpsSq (hmeasG τ hτ)
          (Filter.Eventually.filter_mono (MeasureTheory.ae_mono hle) hmemG)
      have hGbd : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)),
          ‖Real.sqrt (EpsSq α (Gc s))‖ ≤ 2 * Real.sqrt L := by
        filter_upwards [Filter.Eventually.filter_mono (MeasureTheory.ae_mono hle) hbndG]
          with s hs
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        calc Real.sqrt (EpsSq α (Gc s)) ≤ Real.sqrt (4 * L) := Real.sqrt_le_sqrt hs
          _ = 2 * Real.sqrt L := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
                Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
                Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      have hGint : IntervalIntegrable (fun s : ℝ => Real.sqrt (EpsSq α (Gc s)))
          MeasureTheory.volume 0 τ :=
        IntervalIntegrable.mono_fun'
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 2 * Real.sqrt L)
            MeasureTheory.volume 0 τ) hGae hGbd
      calc Real.sqrt (EpsSq α (W τ))
          ≤ ∫ s in (0 : ℝ)..τ, Real.sqrt (EpsSq α (Gc s)) := by
            calc Real.sqrt (EpsSq α (W τ))
                ≤ Real.sqrt ((∫ s in (0 : ℝ)..τ, Real.sqrt (EpsSq α (Gc s))) ^ 2) :=
                  Real.sqrt_le_sqrt (hMink τ hτ)
              _ = |∫ s in (0 : ℝ)..τ, Real.sqrt (EpsSq α (Gc s))| := Real.sqrt_sq_eq_abs _
              _ = ∫ s in (0 : ℝ)..τ, Real.sqrt (EpsSq α (Gc s)) :=
                  abs_of_nonneg (intervalIntegral.integral_nonneg hτ.1
                    (fun u _ => Real.sqrt_nonneg _))
        _ ≤ ∫ s in (0 : ℝ)..τ, Real.sqrt L * Real.sqrt (EpsSq α (W s)) :=
            intervalIntegral.integral_mono_on hτ.1 hGint hLint (fun s hs => by
              have hsI : s ∈ Set.Icc 0 T := ⟨hs.1, le_trans hs.2 hτ.2⟩
              calc Real.sqrt (EpsSq α (Gc s)) ≤ Real.sqrt (L * EpsSq α (W s)) :=
                    Real.sqrt_le_sqrt (hlipW s hsI)
                _ = Real.sqrt L * Real.sqrt (EpsSq α (W s)) := Real.sqrt_mul hL0 _)
        _ = Real.sqrt L * ∫ s in (0 : ℝ)..τ, Real.sqrt (EpsSq α (W s)) :=
            intervalIntegral.integral_const_mul _ _
  -- ## the endgame: the weighted energy vanishes, hence the profile does
  intro τ hτ z θ hz hθ
  have hWsq : EpsSq α (W τ) = 0 :=
    le_antisymm (Real.sqrt_eq_zero'.mp (hgron τ hτ)) (EpsSq_nonneg α (W τ))
  have hmemw := hmemW τ hτ
  have hint : Integrable (fun p : ℝ × ℝ => (W τ p.1 p.2 * epsW α p.1 p.2) ^ 2)
      Work.FTS.StrongEps.EpsLocalPStar.DomM :=
    (Work.FTS.StrongEps.EpsLocalPStar.EpsMem_iff_integrable2).mp hmemw
  have hz0 : (∫ p : ℝ × ℝ, (W τ p.1 p.2 * epsW α p.1 p.2) ^ 2
      ∂Work.FTS.StrongEps.EpsLocalPStar.DomM) = 0 := by
    rw [Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_eq_integral_DomM hmemw]
    exact hWsq
  have hae : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM, W τ p.1 p.2 * epsW α p.1 p.2 = 0 := by
    have h := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun p => sq_nonneg _) hint).mp hz0
    filter_upwards [h] with p hp
    exact sq_eq_zero_iff.mp hp
  have haeQ : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
      W τ p.1 p.2 = 0 := by
    rw [← Work.FTS.StrongEps.EpsLocalPStar.DomM_eq]
    filter_upwards [hae, Work.FTS.StrongEps.EpsLocalPStar.ae_open_DomM] with p hp hpq
    exact (mul_eq_zero.mp hp).resolve_right
      (Work.FTS.StrongEps.EpsSqTools.epsW_ne_zero hpq.1 ⟨hpq.2.1, hpq.2.2⟩)
  have haeQ0 : (fun p : ℝ × ℝ => W τ p.1 p.2)
      =ᵐ[MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0] 0 := by
    refine MeasureTheory.ae_restrict_of_ae_restrict_of_subset ?_ haeQ
    intro p hp
    exact ⟨(Set.mem_Ioi.mp hp.1).le, hp.2.1.le, hp.2.2.le⟩
  have hcont : ContinuousOn (fun p : ℝ × ℝ => W τ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.Galerkin.slice g τ p.1 p.2)
        Work.FTS.EllipticEst.Q0 := ((hcl τ hτ).smoothOpen.forall 0).continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.Galerkin.slice g' τ p.1 p.2)
        Work.FTS.EllipticEst.Q0 := ((hcl' τ hτ).smoothOpen.forall 0).continuousOn
    exact (h1.sub h2).congr (fun p _ => by simp only [hWdef, Pi.sub_apply])
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq haeQ0 Work.FTS.EllipticEst.isOpen_Q0 hcont
    continuousOn_const
  have hzθ := heq (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
  simp only [hWdef, Work.FTS.Galerkin.slice] at hzθ
  exact sub_eq_zero.mp hzθ

end Work.FTS.StrongEps
