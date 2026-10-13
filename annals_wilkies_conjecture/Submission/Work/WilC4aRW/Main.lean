/-
  Area `WilC4aRW` — **real simultaneous Weierstrass preparation** (`C4a_RW`).

  Main result: `WilkiesDesign.CG.C4a.C4a_RW_proved : RealWeierstrass`, the frozen sub-hole
  `C4a_RW` of `Submission/Work/Wilkies/CG/C4a/Spec.lean`.

  Route (the "adapter over lean-pool" route of the C4a design):
   * `Dir.exists_direction`: choose a real direction `v ≠ 0` along which none of the germs
     `h i` restricts to a function vanishing near `0` (closedness + empty interior + Baire).
   * `LinEquiv.exists_coordinate_change`: choose real/complex linear coordinates `L`, `Lc` with
     `L (last basis vector) = v`; `Lc` complexifies `L`.
   * `Extend.complexify`: complexify each real-analytic germ `h i` to a germ `F i` on `ℂ^{n+1}`
     agreeing with `h i` on real points (complexification of the power series).
   * `Order.exactOrder_of_nonzero` + lean-pool `classicalComplexWeierstrassPreparation`: the
     complex Weierstrass preparation of `G i = F i ∘ Lc ∘ snocCLM`.
   * `Bridge.real_preparation`: reflection/conjugation (`Conj.conj_analytic_ambient`,
     `WPT.prep_conj`, `Real.eventuallyEq_of_eventuallyEq_ofRealAmbient`) plus uniqueness turns
     the complex preparation into real data `a'`, `u'` with `h i (L x) = u' x * wpoly a' x`.
-/
import Submission.Work.WilC4aRW.Bridge
import Submission.Work.WilC4aRW.Dir.exists_direction
import Submission.Work.WilC4aRW.Extend.complexify
import Submission.Work.WilC4aRW.LinEquiv.exists_coordinate_change
import Submission.Work.WilC4aRW.Order.exactOrder_of_nonzero

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Filter Topology
open scoped Topology BigOperators ComplexConjugate

namespace WilkiesDesign.CG.C4a

open ClassicalComplexWPT

/-- **C4a.RW, proved.**  Simultaneous real Weierstrass preparation: finitely many real-analytic
germs at `0 ∈ ℝ^{n+1}` that vanish at `0` and are not locally zero become, after ONE real linear
change of coordinates `L`, unit times Weierstrass polynomial in the last variable. -/
theorem C4a_RW_proved : RealWeierstrass := by
  intro n k h hA h0 hNZ
  obtain ⟨v, hvne, hv⟩ := Work.WilC4aRW.Dir.exists_direction h hA h0 hNZ
  obtain ⟨L, hL, Lc, hLc, hLc_last⟩ := Work.WilC4aRW.LinEquiv.exists_coordinate_change v hvne
  have key : ∀ i : Fin k, ∃ (d : ℕ) (a : Fin d → (Fin n → ℝ) → ℝ)
      (u : (Fin (n + 1) → ℝ) → ℝ),
      (∀ j, AnalyticAt ℝ (a j) 0 ∧ a j 0 = 0) ∧ AnalyticAt ℝ u 0 ∧ u 0 ≠ 0 ∧
      ∀ᶠ x in nhds (0 : Fin (n + 1) → ℝ), h i (L x) = u x * wpoly a x := by
    intro i
    obtain ⟨p, hp⟩ := hA i
    obtain ⟨F, hF, hFreal⟩ := Work.WilC4aRW.Extend.complexify (h i) p hp
    have hsnoc : ∀ z : ℂ,
        Work.WilC4aRW.snocCLM n ((0 : Base n), z) = z • Pi.single (Fin.last n) (1 : ℂ) := by
      intro z
      funext j
      refine Fin.lastCases ?_ ?_ j
      · simp [Work.WilC4aRW.snocCLM]
      · intro m
        simp [Work.WilC4aRW.snocCLM]
    let G : Ambient n → ℂ := fun z => F (Lc (Work.WilC4aRW.snocCLM n z))
    have hG : AnalyticAt ℂ G 0 := by
      have hF' : AnalyticAt ℂ F
          (((Lc : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ)).comp
            (Work.WilC4aRW.snocCLM n)) 0) := by
        rw [map_zero]; exact hF
      have hcomp := hF'.compContinuousLinearMap
        (u := (Lc : (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ)).comp
          (Work.WilC4aRW.snocCLM n)) (x := 0)
      simpa [G, Function.comp_def] using hcomp
    have hlast : ∀ z : ℂ, lastSlice G z = F (z • Work.WilC4aRW.cplxIncl v) := by
      intro z
      simp only [lastSlice, G, hsnoc z]
      rw [map_smul, hLc_last]
    have hGreal : ∀ᶠ x : Fin (n + 1) → ℝ in nhds 0,
        G (Work.WilC4aRW.ofRealAmbient x) = (h i (L x) : ℂ) := by
      have hLt : Tendsto (L : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (nhds 0) (nhds 0) := by
        have h := (L : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)).continuous.tendsto 0
        simpa using h
      filter_upwards [hLt.eventually hFreal] with x hx
      rw [show G (Work.WilC4aRW.ofRealAmbient x) =
          F (Work.WilC4aRW.cplxIncl (L x)) by
        change F (Lc (Work.WilC4aRW.snocCLM n (Work.WilC4aRW.ofRealAmbient x))) =
          F (Work.WilC4aRW.cplxIncl (L x))
        rw [Work.WilC4aRW.snocCLM_apply_ofRealAmbient, hLc]]
      exact hx
    have hne : ¬ (lastSlice G =ᶠ[nhds (0 : ℂ)] fun _ => 0) := by
      intro hzero
      apply hv i
      have h1 : ∀ᶠ t : ℝ in nhds 0, lastSlice G (t : ℂ) = 0 := by
        have h := hzero.comp_tendsto (Complex.continuous_ofReal.tendsto 0)
        filter_upwards [h] with t ht
        simpa using ht
      have hvt : Tendsto (fun t : ℝ => t • v) (nhds 0) (nhds (0 : Fin (n + 1) → ℝ)) := by
        have hc : Continuous fun t : ℝ => t • v := continuous_id.smul continuous_const
        simpa using hc.tendsto 0
      filter_upwards [h1, hvt.eventually hFreal] with t ht1 ht2
      rw [hlast (t : ℂ)] at ht1
      rw [← Work.WilC4aRW.cplxIncl_smul t v] at ht1
      rw [ht2] at ht1
      exact_mod_cast ht1
    obtain ⟨d, hd⟩ := Work.WilC4aRW.Order.exactOrder_of_nonzero hG hne
    obtain ⟨a, u, hprep, _⟩ := classicalComplexWeierstrassPreparation n d G hG hd
    obtain ⟨a', u', hprops⟩ := Work.WilC4aRW.real_preparation hG hGreal hprep
    exact ⟨d, a', u', hprops⟩
  choose d a u hprops using key
  exact ⟨L, d, a, u, fun i j => (hprops i).1 j,
    fun i => ⟨(hprops i).2.1, (hprops i).2.2.1⟩,
    Filter.eventually_all.mpr fun i => (hprops i).2.2.2⟩

/-- The theorem proves the frozen statement `RealWeierstrass` of the C4a spec. -/
example : RealWeierstrass := C4a_RW_proved

end WilkiesDesign.CG.C4a

namespace Work.WilC4aRW

open ClassicalComplexWPT

/-- Strengthening of `RealWeierstrass` used by the curve-selection step downstream
(`C4a.C4a_CS_step`): besides the frozen conclusion, the units are nonvanishing on a whole
neighbourhood of `0`, so `sign (u i x)` is locally constant. -/
theorem realWeierstrass_units_ne (hW : WilkiesDesign.CG.C4a.RealWeierstrass) :
    ∀ (n k : ℕ) (h : Fin k → (Fin (n + 1) → ℝ) → ℝ),
      (∀ i, AnalyticAt ℝ (h i) 0) → (∀ i, h i 0 = 0) →
      (∀ i, ¬ (h i =ᶠ[nhds (0 : Fin (n + 1) → ℝ)] fun _ => 0)) →
      ∃ (L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) (d : Fin k → ℕ)
        (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (u : Fin k → (Fin (n + 1) → ℝ) → ℝ),
        (∀ i j, AnalyticAt ℝ (a i j) 0 ∧ a i j 0 = 0) ∧
        (∀ i, AnalyticAt ℝ (u i) 0 ∧ u i 0 ≠ 0) ∧
        (∀ᶠ x in nhds (0 : Fin (n + 1) → ℝ), ∀ i, u i x ≠ 0) ∧
        ∀ᶠ x in nhds (0 : Fin (n + 1) → ℝ),
          ∀ i, h i (L x) = u i x * WilkiesDesign.CG.C4a.wpoly (a i) x := by
  intro n k h hA h0 hNZ
  obtain ⟨L, d, a, u, hprep, hunit, hfac⟩ := hW n k h hA h0 hNZ
  refine ⟨L, d, a, u, hprep, hunit, ?_, hfac⟩
  have hne : ∀ i, ∀ᶠ x in nhds (0 : Fin (n + 1) → ℝ), u i x ≠ 0 :=
    fun i => (hunit i).1.continuousAt.eventually_ne (hunit i).2
  exact Filter.eventually_all.mpr hne

end Work.WilC4aRW

namespace WilkiesDesign.CG.C4a

/-- The strengthened form for the proved theorem: the preparation units are nonvanishing
near the origin. -/
theorem C4a_RW_proved_units :
    ∀ (n k : ℕ) (h : Fin k → (Fin (n + 1) → ℝ) → ℝ),
      (∀ i, AnalyticAt ℝ (h i) 0) → (∀ i, h i 0 = 0) →
      (∀ i, ¬ (h i =ᶠ[nhds (0 : Fin (n + 1) → ℝ)] fun _ => 0)) →
      ∃ (L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) (d : Fin k → ℕ)
        (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (u : Fin k → (Fin (n + 1) → ℝ) → ℝ),
        (∀ i j, AnalyticAt ℝ (a i j) 0 ∧ a i j 0 = 0) ∧
        (∀ i, AnalyticAt ℝ (u i) 0 ∧ u i 0 ≠ 0) ∧
        (∀ᶠ x in nhds (0 : Fin (n + 1) → ℝ), ∀ i, u i x ≠ 0) ∧
        ∀ᶠ x in nhds (0 : Fin (n + 1) → ℝ),
          ∀ i, h i (L x) = u i x * wpoly (a i) x :=
  Work.WilC4aRW.realWeierstrass_units_ne C4a_RW_proved

end WilkiesDesign.CG.C4a
