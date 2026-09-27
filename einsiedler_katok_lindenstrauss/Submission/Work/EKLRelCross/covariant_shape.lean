import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.condExp_comap_aDiag
import Submission.Work.EKLC6Core.isPlaqueAlgebra_comap
import Submission.Work.EKLC6Core.shape_comap_conj
import Submission.Work.EKLC6Core.shape_mass_pos
import Submission.Work.EKLComp.LeafAux

/-!
# `Work.EKLRelCross.covariant_shape` — Pisa 7.17 on the shape of a plaque algebra

The `A`-covariance of a system of leafwise measures, restricted to the shape of a plaque
algebra: for `μ`-a.e. `x`, if `x` and `T x = aDiag t • x` lie in the conull domain of the
leafwise system, `T x` lies in the plaquing set `Z`, and the stabiliser of `T x` in `U` is
trivial, then `ν (T x)` and the conjugate of `ν x` are proportional on the shape of the atom at
`T x`, with a constant independent of the test set.

The argument is the paper's (Pisa 7.17, EKL (4)).  Since `Z ∈ m`, the transported σ-algebra
`comap T m` is a plaque algebra for `U` on `T ⁻¹' Z` whose atom at `x` is `T ⁻¹' [T x]_m`
(`Work.EKLC6Core.isPlaqueAlgebra_comap`), so its shape at `x` is the `aDiag (-t)`-conjugate of
the shape of `m` at `T x` (`Work.EKLC6Core.shape_comap_conj`).  Applying the `condexp` field of
`IsLeafwise` at `(Z, m)` and at `(T ⁻¹' Z, comap T m)`, and transporting the conditional
expectation along the measure-preserving map `T` (`Work.EKLRelCross.condExp_comap_aDiag`), gives,
for every bounded Borel `f` on `X₃`,

`∫_{S} f (u • T x) dν (T x) / ν (T x) (S) = ∫_{K} f (T (u • x)) dν x / ν x (K)`,

`S = shape m U (T x)`, `K = shape (comap T m) U x`.  Testing on the indicators of the countable
π-system `Work.EKLComp.piBasis` turns this into the proportionality of the two pushforwards of
the leafwise measures under the orbit map `u ↦ u • T x`; that map is injective on `S` because the
stabiliser of `T x` in `U` is trivial, and the pushforward of `ν (T x) ↾ S` under an injective
orbit map is the measure `ν (T x)` itself (`mass_map_restrict_image_eq`).  Hence `ν (T x)` and
`(ν x).map (aDiag t · aDiag (-t))` are proportional on `S`, with the constant
`ν (T x) (S) / ν x (K)`.

## A note on instance capture

The statements below mention both the Borel σ-algebra of `X₃` and an arbitrary sub-σ-algebra `m`.
Lean resolves the implicit `MeasurableSpace X₃` argument of `Measure`, `MeasurableSet` and
`condExp` by searching the local context, and a local hypothesis of class type (such as
`m : MeasurableSpace X₃`) *is* picked up there; statements about `m` are therefore routed through
the wrapper `MAlgX` (a structure, never an instance), so that the Borel σ-algebra is always the
global instance `Work.EKLContract.instMeasurableSpaceX3`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract.Lemmas

/-! ## Vocabulary -/

/-- Wrapper for a σ-algebra on `X₃`: a structure rather than a local hypothesis, so that
typeclass search for `MeasurableSpace X₃` never captures it. -/
structure MAlgX where
  m : MeasurableSpace X3

/-- The action of `aDiag t` on `X₃`. -/
def smulDiag (t : Fin 3 → ℝ) (x : X3) : X3 := aDiag t • x

/-- The σ-algebra `comap (aDiag t ·) m`.  Spelled as a `def` (not a local `set`) so that it is
not picked up by instance search. -/
def aDiagComap (t : Fin 3 → ℝ) (m : MeasurableSpace X3) : MeasurableSpace X3 :=
  MeasurableSpace.comap (smulDiag t) m

/-- Conjugation by `aDiag t` on `SL₃(ℝ)`, as a measurable map. -/
theorem measurable_conjBy_aDiag (t : Fin 3 → ℝ) :
    Measurable (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) :=
  ((continuous_const.mul continuous_id).mul continuous_const).measurable

/-! ## Two elementary computations -/

/-- The set integral of the indicator of `B` along the orbit of `y` is the mass of `B` for the
pushforward of `ρ ↾ W` under the orbit map. -/
theorem setIntegral_indicator_orbit_eq_map_apply {y : X3} {W : Set SL3} {B : Set X3}
    (hW : MeasurableSet W) (hB : MeasurableSet B) (ρ : Measure SL3) :
    (∫ u in W, (B.indicator fun _ => (1 : ℝ)) (u • y) ∂ρ)
      = ((ρ.restrict W).map (fun u : SL3 => u • y) B).toReal := by
  classical
  have hφ : Measurable (fun u : SL3 => u • y) := by fun_prop
  have hpre : MeasurableSet ((fun u : SL3 => u • y) ⁻¹' B) := hB.preimage hφ
  have hfun : (fun u : SL3 => (B.indicator fun _ => (1 : ℝ)) (u • y))
      = ((fun u : SL3 => u • y) ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
    funext u
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : u • y ∈ B <;> simp [h]
  rw [hfun, MeasureTheory.setIntegral_indicator hpre, MeasureTheory.setIntegral_const,
    smul_eq_mul, mul_one, MeasureTheory.measureReal_def]
  rw [Measure.map_apply hφ hB, Measure.restrict_apply' hW]
  rw [Set.inter_comm]

/-- The mass of the orbit image of a set on which the orbit map is injective. -/
theorem mass_map_restrict_image_eq {y : X3} {W C : Set SL3}
    (hW : MeasurableSet W) (hC : MeasurableSet C) (hCW : C ⊆ W)
    (hinj : Set.InjOn (fun u : SL3 => u • y) W) (ρ : Measure SL3) :
    ((ρ.restrict W).map (fun u : SL3 => u • y)) ((fun u : SL3 => u • y) '' C) = ρ C := by
  haveI : PolishSpace SL3 := polishSpace_specialLinearGroup
  have hφ : Measurable (fun u : SL3 => u • y) := by fun_prop
  have hcont : ContinuousOn (fun u : SL3 => u • y) C := by fun_prop
  have hIm : MeasurableSet ((fun u : SL3 => u • y) '' C) :=
    MeasurableSet.image_of_continuousOn_injOn hC hcont (hinj.mono hCW)
  rw [Measure.map_apply hφ hIm, Measure.restrict_apply' hW]
  have hset : (fun u : SL3 => u • y) ⁻¹' ((fun u : SL3 => u • y) '' C) ∩ W = C := by
    ext u; constructor
    · rintro ⟨⟨c, hc, hcu⟩, huW⟩
      have h : u = c := hinj huW (hCW hc) hcu.symm
      rw [h]; exact hc
    · intro huC
      exact ⟨⟨u, huC, rfl⟩, hCW huC⟩
  rw [hset]

/-! ## The main computation, with the σ-algebra wrapped -/

theorem covariant_shape_aux {U : Subgroup SL3} (hU : IsHoro U)
    {μ : Measure X3} [IsProbabilityMeasure μ]
    {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X') (t : Fin 3 → ℝ)
    (ht : MeasurePreserving (smulDiag t) μ μ)
    {Z : Set X3} (S : MAlgX) (hpla : IsPlaqueAlgebra U Z S.m) :
    ∀ᵐ x ∂μ, x ∈ X' → smulDiag t x ∈ X' → smulDiag t x ∈ Z →
      (∀ u ∈ U, u • (smulDiag t x) = smulDiag t x → u = 1) →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ C : Set SL3, MeasurableSet C →
        C ⊆ shape S.m U (smulDiag t x) →
        ν (smulDiag t x) C =
          c * (ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) C := by
  classical
  have hmle : S.m ≤ borel X3 := hpla.1
  have hZbor : MeasurableSet Z := hmle Z hpla.2.2.1
  have hTmeas : Measurable (smulDiag t) := (continuous_const_smul (aDiag t)).measurable
  have hZ'bor : MeasurableSet (smulDiag t ⁻¹' Z) := hZbor.preimage hTmeas
  have hpla' : IsPlaqueAlgebra U (smulDiag t ⁻¹' Z) (aDiagComap t S.m) :=
    Work.EKLC6Core.isPlaqueAlgebra_comap hU t hpla
  have hsmulmeas : ∀ y : X3, Measurable (fun u : SL3 => u • y) := fun y => by fun_prop
  -- the key a.e. identity, for the indicators of the countable π-system
  have hkey : ∀ᵐ x ∂μ, ∀ B ∈ Work.EKLComp.piBasis, smulDiag t x ∈ Z →
      (∫ u in shape S.m U (smulDiag t x),
            (B.indicator fun _ => (1 : ℝ)) (u • (smulDiag t x)) ∂(ν (smulDiag t x))) /
          ((ν (smulDiag t x)) (shape S.m U (smulDiag t x))).toReal
        = (∫ u in shape (aDiagComap t S.m) U x,
              (B.indicator fun _ => (1 : ℝ)) (smulDiag t (u • x)) ∂(ν x)) /
          ((ν x) (shape (aDiagComap t S.m) U x)).toReal := by
    rw [eventually_countable_ball Work.EKLComp.countable_piBasis]
    intro B hB
    have hBmeas : MeasurableSet B := Work.EKLComp.measurableSet_of_mem_piBasis hB
    have hFmeas : Measurable (B.indicator fun _ => (1 : ℝ)) :=
      Measurable.indicator measurable_const hBmeas
    have hFbdd : ∃ K, ∀ y, |(B.indicator fun _ => (1 : ℝ)) y| ≤ K :=
      ⟨1, fun y => by rw [Set.indicator_apply]; split <;> simp⟩
    have hFbddc : ∃ K, ∀ y : X3, |((B.indicator fun _ => (1 : ℝ)) ∘ (smulDiag t)) y| ≤ K :=
      ⟨hFbdd.choose, fun y => by
        simpa only [Function.comp_apply] using hFbdd.choose_spec (smulDiag t y)⟩
    have hc1 : ∀ᵐ z ∂(μ.restrict Z),
        condExp S.m (μ.restrict Z) (B.indicator fun _ => (1 : ℝ)) z =
          (∫ u in shape S.m U z, (B.indicator fun _ => (1 : ℝ)) (u • z) ∂(ν z)) /
            ((ν z) (shape S.m U z)).toReal :=
      hL.condexp Z S.m hpla _ hFmeas hFbdd
    have h1 : ∀ᵐ x ∂μ, smulDiag t x ∈ Z →
        condExp S.m (μ.restrict Z) (B.indicator fun _ => (1 : ℝ)) (smulDiag t x)
          = (∫ u in shape S.m U (smulDiag t x),
                (B.indicator fun _ => (1 : ℝ)) (u • (smulDiag t x)) ∂(ν (smulDiag t x))) /
              ((ν (smulDiag t x)) (shape S.m U (smulDiag t x))).toReal :=
      ht.quasiMeasurePreserving.ae ((ae_restrict_iff' hZbor).mp hc1)
    have hc2 : ∀ᵐ y ∂(μ.restrict (smulDiag t ⁻¹' Z)),
        condExp (aDiagComap t S.m) (μ.restrict (smulDiag t ⁻¹' Z))
            ((B.indicator fun _ => (1 : ℝ)) ∘ (smulDiag t)) y =
          (∫ u in shape (aDiagComap t S.m) U y,
              ((B.indicator fun _ => (1 : ℝ)) ∘ (smulDiag t)) (u • y) ∂(ν y)) /
            ((ν y) (shape (aDiagComap t S.m) U y)).toReal :=
      hL.condexp (smulDiag t ⁻¹' Z) (aDiagComap t S.m) hpla' _ (hFmeas.comp hTmeas) hFbddc
    have hnat : ∀ᵐ y ∂(μ.restrict (smulDiag t ⁻¹' Z)),
        condExp (aDiagComap t S.m) (μ.restrict (smulDiag t ⁻¹' Z))
            ((B.indicator fun _ => (1 : ℝ)) ∘ (smulDiag t)) y =
          condExp S.m (μ.restrict Z) (B.indicator fun _ => (1 : ℝ)) (smulDiag t y) :=
      Work.EKLRelCross.condExp_comap_aDiag (Z := Z) (f := B.indicator fun _ => (1 : ℝ))
        t ht S.m hmle hpla.2.2.1 hFmeas hFbdd
    have hcomb : ∀ᵐ y ∂(μ.restrict (smulDiag t ⁻¹' Z)),
        (∫ u in shape (aDiagComap t S.m) U y,
            (B.indicator fun _ => (1 : ℝ)) (smulDiag t (u • y)) ∂(ν y)) /
          ((ν y) (shape (aDiagComap t S.m) U y)).toReal
        = condExp S.m (μ.restrict Z) (B.indicator fun _ => (1 : ℝ)) (smulDiag t y) :=
      (hc2.and hnat).mono (fun y h => h.1.symm.trans h.2)
    have h2 : ∀ᵐ x ∂μ, smulDiag t x ∈ Z →
        (∫ u in shape (aDiagComap t S.m) U x,
            (B.indicator fun _ => (1 : ℝ)) (smulDiag t (u • x)) ∂(ν x)) /
          ((ν x) (shape (aDiagComap t S.m) U x)).toReal
        = condExp S.m (μ.restrict Z) (B.indicator fun _ => (1 : ℝ)) (smulDiag t x) := by
      have h := (ae_restrict_iff' hZ'bor).mp hcomb
      filter_upwards [h] with x hx hTxZ
      exact hx hTxZ
    filter_upwards [h1, h2] with x h1x h2x hTxZ
    exact (h1x hTxZ).symm.trans (h2x hTxZ).symm
  filter_upwards [hkey] with x hx
  intro hxX hTxX hTxZ hstab
  -- the two shapes
  set St : Set SL3 := shape S.m U (smulDiag t x) with hSt
  set K : Set SL3 := shape (aDiagComap t S.m) U x with hK
  have hKconj : K = Work.EKLC6Core.conjBy (-t) St := by
    rw [hK, hSt]
    exact Work.EKLC6Core.shape_comap_conj hU t x
  have hxZ' : x ∈ smulDiag t ⁻¹' Z := hTxZ
  have hStmeas : MeasurableSet St := by
    obtain ⟨O, hO, hOshape⟩ := (hpla.2.2.2 (smulDiag t x) hTxZ).2.2.1
    rw [hSt, hOshape]
    exact hO.measurableSet.inter hU.1.measurableSet
  have hKmeas : MeasurableSet K := by
    obtain ⟨O, hO, hOshape⟩ := (hpla'.2.2.2 x hxZ').2.2.1
    rw [hK, hOshape]
    exact hO.measurableSet.inter hU.1.measurableSet
  -- masses
  have hmass1 : 0 < ν (smulDiag t x) St ∧ ν (smulDiag t x) St < ⊤ := by
    have h := Work.EKLC6Core.shape_mass_pos (A := S.m) (Z := Z) hL hpla hTxX hTxZ
    rw [← hSt] at h
    exact h
  have hmass2 : 0 < ν x K ∧ ν x K < ⊤ := by
    have h := Work.EKLC6Core.shape_mass_pos (A := aDiagComap t S.m) (Z := smulDiag t ⁻¹' Z)
      hL hpla' hxX hxZ'
    rw [← hK] at h
    exact h
  have hc1ne : ν (smulDiag t x) St ≠ 0 ∧ ν (smulDiag t x) St ≠ ⊤ :=
    ⟨ne_of_gt hmass1.1, ne_of_lt hmass1.2⟩
  have hd2ne : ν x K ≠ 0 ∧ ν x K ≠ ⊤ := ⟨ne_of_gt hmass2.1, ne_of_lt hmass2.2⟩
  -- the conjugated measure
  set μ' : Measure SL3 := (ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) with hμ'
  have hpre : (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹' St = K := by
    rw [hKconj]
    ext u
    rw [Set.mem_preimage, Work.EKLC6Core.mem_conjBy_neg]
  have hμ'St : μ' St = ν x K := by
    rw [hμ', Measure.map_apply (measurable_conjBy_aDiag t) hStmeas, hpre]
  have hd2ne' : μ' St ≠ 0 ∧ μ' St ≠ ⊤ := by rw [hμ'St]; exact hd2ne
  have hμ'St_lt : μ' St < ⊤ := by rw [hμ'St]; exact hmass2.2
  -- the two pushforwards
  set ρ1 : Measure X3 :=
    ((ν (smulDiag t x)).restrict St).map (fun u : SL3 => u • (smulDiag t x)) with hρ1
  set ρ2 : Measure X3 := (μ'.restrict St).map (fun u : SL3 => u • (smulDiag t x)) with hρ2
  have hsmulmeasx : Measurable (fun u : SL3 => u • (smulDiag t x)) := hsmulmeas _
  have hρ1fin : IsFiniteMeasure ρ1 := ⟨by
    rw [hρ1, Measure.map_apply hsmulmeasx MeasurableSet.univ, Set.preimage_univ,
      Measure.restrict_apply' hStmeas, Set.univ_inter]
    exact hmass1.2⟩
  -- the value of the two integrals against the indicators of the π-system
  have hval1 : ∀ B ∈ Work.EKLComp.piBasis,
      (∫ u in shape S.m U (smulDiag t x),
          (B.indicator fun _ => (1 : ℝ)) (u • (smulDiag t x)) ∂(ν (smulDiag t x)))
        = (ρ1 B).toReal := by
    intro B hB
    have hBmeas : MeasurableSet B := Work.EKLComp.measurableSet_of_mem_piBasis hB
    have h1 : (∫ u in shape S.m U (smulDiag t x),
          (B.indicator fun _ => (1 : ℝ)) (u • (smulDiag t x)) ∂(ν (smulDiag t x)))
        = ∫ u in St, (B.indicator fun _ => (1 : ℝ)) (u • (smulDiag t x))
            ∂(ν (smulDiag t x)) := by
      rw [hSt]
    rw [h1, hρ1]
    exact setIntegral_indicator_orbit_eq_map_apply hStmeas hBmeas (ν (smulDiag t x))
  have hval2 : ∀ B ∈ Work.EKLComp.piBasis,
      (∫ u in shape (aDiagComap t S.m) U x,
          (B.indicator fun _ => (1 : ℝ)) (smulDiag t (u • x)) ∂(ν x)) = (ρ2 B).toReal := by
    intro B hB
    have hBmeas : MeasurableSet B := Work.EKLComp.measurableSet_of_mem_piBasis hB
    have hconjmeas : Measurable (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) :=
      measurable_conjBy_aDiag t
    have hTconj : ∀ u : SL3, smulDiag t (u • x) =
        (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) u • (smulDiag t x) := by
      intro u
      show aDiag t • (u • x) = (aDiag t * u * (aDiag t)⁻¹) • (aDiag t • x)
      rw [← mul_smul, ← mul_smul]
      congr 1
      group
    have hpre2 : (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) ⁻¹' St = K := hpre
    have hstep : (∫ v in St, (B.indicator fun _ => (1 : ℝ)) (v • (smulDiag t x)) ∂μ')
        = ∫ u in K, (B.indicator fun _ => (1 : ℝ))
            ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) u • (smulDiag t x)) ∂(ν x) := by
      have h := MeasureTheory.setIntegral_map (μ := ν x)
        (g := fun g : SL3 => aDiag t * g * (aDiag t)⁻¹)
        (f := fun v : SL3 => (B.indicator fun _ => (1 : ℝ)) (v • (smulDiag t x)))
        hStmeas
        ((Measurable.indicator measurable_const (hBmeas.preimage hsmulmeasx)).aestronglyMeasurable)
        hconjmeas.aemeasurable
      rw [← hμ', hpre2] at h
      exact h
    calc (∫ u in shape (aDiagComap t S.m) U x,
            (B.indicator fun _ => (1 : ℝ)) (smulDiag t (u • x)) ∂(ν x))
        = ∫ u in K, (B.indicator fun _ => (1 : ℝ)) (smulDiag t (u • x)) ∂(ν x) := by rw [hK]
      _ = ∫ u in K, (B.indicator fun _ => (1 : ℝ))
            ((fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) u • (smulDiag t x)) ∂(ν x) :=
          MeasureTheory.setIntegral_congr_fun hKmeas (fun u _ => by rw [hTconj u])
      _ = ∫ v in St, (B.indicator fun _ => (1 : ℝ)) (v • (smulDiag t x)) ∂μ' := hstep.symm
      _ = (ρ2 B).toReal := by
          rw [hρ2]
          exact setIntegral_indicator_orbit_eq_map_apply hStmeas hBmeas μ'
  -- proportionality on the π-system
  set θ : ENNReal := ν (smulDiag t x) St / μ' St with hθ
  have hθ0 : θ ≠ 0 := (ENNReal.div_ne_zero).mpr ⟨hc1ne.1, hd2ne'.2⟩
  have hθT : θ ≠ ⊤ := ENNReal.div_ne_top hc1ne.2 hd2ne'.1
  have hprop : ∀ B ∈ Work.EKLComp.piBasis, ρ1 B = θ * ρ2 B := by
    intro B hB
    have hBmeas : MeasurableSet B := Work.EKLComp.measurableSet_of_mem_piBasis hB
    have hk := hx B hB hTxZ
    rw [hval1 B hB, hval2 B hB] at hk
    have hd1 : (ν (smulDiag t x)) (shape S.m U (smulDiag t x)) = ν (smulDiag t x) St := by
      rw [hSt]
    have hd2 : (ν x) (shape (aDiagComap t S.m) U x) = μ' St := by rw [hμ'St, hK]
    rw [hd1, hd2] at hk
    have hr1 : (ν (smulDiag t x) St).toReal ≠ 0 := by
      simp only [ENNReal.toReal_ne_zero]; exact hc1ne
    have hr2 : (μ' St).toReal ≠ 0 := by
      simp only [ENNReal.toReal_ne_zero]; exact hd2ne'
    have hcross : (ρ1 B).toReal * (μ' St).toReal
        = (ρ2 B).toReal * (ν (smulDiag t x) St).toReal :=
      (div_eq_div_iff hr1 hr2).mp hk
    have hB1 : ρ1 B ≤ ν (smulDiag t x) St := by
      rw [hρ1, Measure.map_apply hsmulmeasx hBmeas, Measure.restrict_apply' hStmeas]
      exact measure_mono (Set.inter_subset_right)
    have hB2 : ρ2 B ≤ μ' St := by
      rw [hρ2, Measure.map_apply hsmulmeasx hBmeas, Measure.restrict_apply' hStmeas]
      exact measure_mono (Set.inter_subset_right)
    have hf1 : ρ1 B ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hB1 hmass1.2)
    have hf2 : ρ2 B ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hB2 hμ'St_lt)
    have hprod1 : (ρ1 B * μ' St).toReal = (ρ2 B * (ν (smulDiag t x) St)).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
      exact hcross
    have hf1' : ρ1 B * μ' St ≠ ⊤ := ENNReal.mul_ne_top hf1 hd2ne'.2
    have hf2' : ρ2 B * (ν (smulDiag t x) St) ≠ ⊤ := ENNReal.mul_ne_top hf2 hc1ne.2
    have hENN : ρ1 B * μ' St = ρ2 B * (ν (smulDiag t x) St) := by
      rcases (ENNReal.toReal_eq_toReal_iff _ _).mp hprod1 with h | h | h
      · exact h
      · exact absurd h.2 hf2'
      · exact absurd h.1 hf1'
    calc ρ1 B = ρ1 B * (μ' St * (μ' St)⁻¹) := by
          rw [ENNReal.mul_inv_cancel hd2ne'.1 hd2ne'.2, mul_one]
      _ = (ρ1 B * μ' St) * (μ' St)⁻¹ := by rw [mul_assoc]
      _ = (ρ2 B * (ν (smulDiag t x) St)) * (μ' St)⁻¹ := by rw [hENN]
      _ = θ * ρ2 B := by
          rw [hθ, ENNReal.div_eq_inv_mul]
          ring
  have hρeq : ρ1 = θ • ρ2 := by
    haveI : IsFiniteMeasure ρ1 := hρ1fin
    refine Work.EKLComp.ext_of_piBasis (fun B hB => ?_) ?_
    · rw [Measure.smul_apply, smul_eq_mul]
      exact hprop B hB
    · rw [Measure.smul_apply, smul_eq_mul]
      have h1 : ρ1 Set.univ = ν (smulDiag t x) St := by
        rw [hρ1, Measure.map_apply hsmulmeasx MeasurableSet.univ, Set.preimage_univ,
          Measure.restrict_apply' hStmeas, Set.univ_inter]
      have h2 : ρ2 Set.univ = μ' St := by
        rw [hρ2, Measure.map_apply hsmulmeasx MeasurableSet.univ, Set.preimage_univ,
          Measure.restrict_apply' hStmeas, Set.univ_inter]
      rw [h1, h2, hθ]
      exact (ENNReal.div_mul_cancel hd2ne'.1 hd2ne'.2).symm
  -- the orbit map is injective on the shape
  have hinjSt : Set.InjOn (fun u : SL3 => u • (smulDiag t x)) St := by
    intro u hu v hv huv
    have huU : u ∈ U := (by rw [hSt] at hu; exact hu.1)
    have hvU : v ∈ U := (by rw [hSt] at hv; exact hv.1)
    have huv' : u • (smulDiag t x) = v • (smulDiag t x) := huv
    have hfix : (v⁻¹ * u) • (smulDiag t x) = smulDiag t x := by
      have h : v⁻¹ • (u • (smulDiag t x)) = v⁻¹ • (v • (smulDiag t x)) := by rw [huv']
      rw [inv_smul_smul, ← mul_smul] at h
      exact h
    have h1 : v⁻¹ * u = 1 := hstab _ (U.mul_mem (U.inv_mem hvU) huU) hfix
    calc u = v * (v⁻¹ * u) := by group
      _ = v := by rw [h1, mul_one]
  -- conclusion
  refine ⟨θ, hθ0, hθT, ?_⟩
  intro C hC hCS
  have hρ1C : ρ1 ((fun u : SL3 => u • (smulDiag t x)) '' C) = ν (smulDiag t x) C := by
    rw [hρ1]
    exact mass_map_restrict_image_eq hStmeas hC hCS hinjSt (ν (smulDiag t x))
  have hρ2C : ρ2 ((fun u : SL3 => u • (smulDiag t x)) '' C) = μ' C := by
    rw [hρ2]
    exact mass_map_restrict_image_eq hStmeas hC hCS hinjSt μ'
  calc ν (smulDiag t x) C
      = ρ1 ((fun u : SL3 => u • (smulDiag t x)) '' C) := hρ1C.symm
    _ = (θ • ρ2) ((fun u : SL3 => u • (smulDiag t x)) '' C) := by rw [hρeq]
    _ = θ * ρ2 ((fun u : SL3 => u • (smulDiag t x)) '' C) := by
        rw [Measure.smul_apply, smul_eq_mul]
    _ = θ * μ' C := by rw [hρ2C]
    _ = θ * (ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) C := by rw [hμ']

/-! ## The requested statement -/

theorem covariant_shape {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {X' : Set Work.EKLContract.X3}
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (t : Fin 3 → ℝ)
    (ht : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {Z : Set Work.EKLContract.X3} {mm : MeasurableSpace Work.EKLContract.X3}
    (hpla : Work.EKLContract.IsPlaqueAlgebra U Z mm) (hμZ : μ Z ≠ 0) :
    ∀ᵐ x ∂μ, x ∈ X' → Work.EKLContract.aDiag t • x ∈ X' → Work.EKLContract.aDiag t • x ∈ Z →
      (∀ u ∈ U, u • (Work.EKLContract.aDiag t • x) = Work.EKLContract.aDiag t • x → u = 1) →
      ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ C : Set Work.EKLContract.SL3, MeasurableSet C →
        C ⊆ Work.EKLContract.shape mm U (Work.EKLContract.aDiag t • x) →
        ν (Work.EKLContract.aDiag t • x) C =
          c * (ν x).map (fun g : Work.EKLContract.SL3 => Work.EKLContract.aDiag t * g * (Work.EKLContract.aDiag t)⁻¹) C := by
  exact covariant_shape_aux (μ := μ) (ν := ν) (X' := X') hU hL t ht ⟨mm⟩ hpla

end Work.EKLRelCross
