import Submission.Work.Wilkies.Holes
import Submission.Work.WilC0.Main
import Submission.Work.WilC1.Main
import Submission.Work.WilC2.Main
import Submission.Work.WilC4.Wire
import Submission.Work.WilC5.Main
import Submission.Work.WilC6.C6
import Submission.Work.WilVP.ValProp_TR
import Submission.Work.WilC4aTS.TS
import Submission.Work.WilC4aAL.Main
import Submission.Work.WilC4aA.Main
import Submission.Work.WilC4aP.Main
import Submission.Work.WilC4aCS.CurveSelStep
import Submission.Work.WilC4aL.Target
import Submission.Work.WilC4aRW.Main
import Submission.Work.WilC4aU.Main
import Submission.Work.WilG1.Main
import Submission.Work.WilG4b.G4_bdd_dx_proved
import Submission.Work.WilG5.Main
import Submission.Work.WilG4a.Base
import Submission.Work.WilG4a.Zero
import Submission.Work.WilG4cW.G4stepW
import Submission.Work.WilE2.E2_components_proved
import Submission.Work.WilE2.E2_khovanskii_proved
import Submission.Work.WilE2.regular_values_dense
import Submission.Work.WilE3.Identity.E3_identity_proved
import Submission.Work.WilE3K.Main
import Submission.Work.WilE5.E5
import Submission.Work.WilE7.Main
import Submission.Work.WilE8.Assemble
import Submission.Work.WilE8.Final
import Submission.Work.WilE9G.EffStratAE_of_frozen
import Submission.Work.WilE9.Sharp.Assembly
import Submission.Work.WilE10.RexpSubMain
import Submission.Work.WilE10.SubPfRexpMain
import Submission.Work.WilE10.UnifFiniteMain
import Submission.Work.WilE7.E7_prop_main_proved
import Submission.Work.WilE7.E7_fiber_cut_proved
import Submission.Work.WilE6.E6_fiber_closure_proved
import Submission.Work.WilE3.Taylor.E3_taylor_closure_proved_hK
import Submission.Work.WilE4.E4

/-!
# Wilkies final wire, conditional on E7 (curric-46 lead, 2026-10-12)

`corollary_1_of_prop9 (hP9 : Work.WilE7.Prop9)` proves the frozen `WilkiesDesign.corollary_1`
statement from the delivered areas, with the single remaining hypothesis `Prop9`
(= the frozen `E.E7_prop_main`, being proved by area E7). No frozen spec hole is used:
the spec's `*_wiring` theorems are re-done here with the delivered `*_proved` terms.
Deviations from the frozen spec (all reviewed rulings): G4 uses `F1AffineW` (frozen `F1Affine`
is false); C5 takes `hVP := ValProp_TR`; the E instance is WilE8's own `genSOMin`.
-/

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilFinal
open WilkiesConjecture WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.E (eaEval)

/-! ## E side -/

/-- E0: the theorem of the complement for ℝ_rexp (E10 + E7's sub-Pfaffian complement). -/
theorem E0_rexp_complement' (hP9 : Work.WilE7.Prop9) {n : ℕ} (X : Set (Fin n → ℝ))
    (h : RExpExist X) : RExpExist Xᶜ := by
  obtain ⟨Z, hZ, rfl⟩ := E.E10_rexp_to_subpf_proved X h
  have key := E.E10_subpf_to_rexp_proved _ (E.E7_subpf_compl_proved hP9 Z hZ)
  have hset : (E.psiV ⁻¹' (E.cubeC n \ Z)) = (E.psiV ⁻¹' Z)ᶜ := by
    ext x; simp [E.psiV_mem_cube x]
  rw [hset] at key; exact key

/-- E9's sharp derivatives stated for `Gen` directly (the proof body of
`Work.WilE9.E9_sharpDeriv_of_EffStratAE` after its `sharpDerivGen_iff.mpr`, which would
otherwise drag the spec's `genSOMin` — and its frozen `E8_comps` — into the closure). -/
theorem sharpDerivGen_direct
    (hE2 : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k),
      X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧ ↑s ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y)
    (hEff : Work.WilE9G.EffStratAE)
    (hE8 : ∀ F n : ℕ, ∃ (a : ℕ) (p : Polynomial ℕ), p.eval 0 = 0 ∧
      ∀ (D : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.E.Gen F D n X →
        WilkiesDesign.E.StarR a (p.eval D) n X) :
    Work.WilE9.SharpDerivGen := by
  intro F n
  obtain ⟨a₁, b₁, hlayer⟩ :=
    Work.WilE9.Sharp.layer_strata hE8 (fun h => Work.Sharp.star_exists_length_le h) hEff F n
  obtain ⟨aD, bD, hDomGen⟩ := Work.WilE9.Sharp.DomSet2_gen hE2 n a₁ F
  obtain ⟨aE, bE, hEsetGen⟩ := Work.WilE9.Sharp.Eset_gen hE2 n a₁
  obtain ⟨b, hb⟩ := Work.WilE9.Sharp.poly_eval_compose_bound bD bE Polynomial.X b₁ a₁
  have hb' : ∀ D k : ℕ,
      MvPolynomial.eval ![D, b₁.eval D, k, a₁] bD +
        MvPolynomial.eval ![b₁.eval D, k, a₁] bE ≤ MvPolynomial.eval ![D, k] b := by
    intro D k
    simpa only [Polynomial.eval_X] using hb D k
  refine ⟨max (aD + 1) aE + 1, b, ?_⟩
  intro D f hgr k v
  obtain ⟨Z, S, hZS, hSlen, hSdata, hN, hNvol, hcov⟩ := hlayer D f hgr
  have hGood : ∀ A ∈ S, A.E.Good := fun A hA => (hSdata A hA).2.2.2.1
  have hfmtS : ∀ A ∈ S, A.E.X.fmt ≤ a₁ := fun A hA => (hSdata A hA).1
  have hdegS : ∀ A ∈ S, A.E.deg ≤ b₁.eval D := fun A hA => (hSdata A hA).2.1
  have hblS : ∀ A ∈ S, A.E.X.basics.length ≤ b₁.eval D + 1 :=
    fun A hA => (hSdata A hA).2.2.1
  have hπS : ∀ A ∈ S, ∀ w ∈ A.comp, Work.WilE9.Sharp.stratProj w ∈ Z :=
    fun A hA => (hSdata A hA).2.2.2.2.2
  have hlenS : S.length ≤ b₁.eval D + 1 := by omega
  -- the IFT-based locality of the zero set of a `Good` stratum
  have hQ : ∀ A ∈ S, ∀ z ∈ A.comp, ∀ᶠ z' in nhds z,
      (∀ a, eaEval A.E.X.c (A.E.h a) z' = 0) → z' ∈ A.comp := by
    intro A hA z hz
    have hzX : z ∈ A.E.X.set := connectedComponentIn_subset A.E.X.set A.q hz
    have hloc := Work.WilE9.Sharp.AE.component_locality A.E (hGood A hA) z hzX
    have heq : connectedComponentIn A.E.X.set z = A.comp := (connectedComponentIn_eq hz).symm
    filter_upwards [hloc] with z' hz'
    rwa [heq] at hz'
  obtain ⟨hspec, hperm⟩ := Work.WilE9.Sharp.layer_spec (S := S) hZS hGood hπS ⟨hN, hNvol, hcov⟩
    (fun A hA L y σ hex => by
      obtain ⟨z, hz, hzout⟩ := hex
      exact (Work.WilE9.Sharp.exSemiPf_base_gen hZS A.E A.comp (hπS A hA) L y σ
        ⟨z, Work.WilE9.Sharp.AE.exComp_subset_set A.E A.q L hz, hzout,
          Work.WilE9.Sharp.AE.exStrat_mem_comp_of_mem_exComp A.E A.q L hz⟩).2)
    (fun A hA L x w hw hbase => by
      obtain ⟨z, hz, hzout, hzQ⟩ :=
        Work.WilE9.Sharp.exSemiPf_fst_gen hZS A.E (hGood A hA) A.comp (hQ A hA) (hπS A hA)
          L x w (connectedComponentIn_subset A.E.X.set A.q hw) hw hbase
      exact ⟨z, Work.WilE9.Sharp.mem_exComp_of_mem_set A.E A.q L hz hzQ, hzout⟩)
    (fun A hA L y σ hex => by
      obtain ⟨z, hz, hzout⟩ := hex
      exact Work.WilE9.Sharp.exSemiPf_snd_gen hZS A.E (hGood A hA) A.comp (hQ A hA) (hπS A hA)
        L y σ ⟨z, Work.WilE9.Sharp.AE.exComp_subset_set A.E A.q L hz, hzout,
          Work.WilE9.Sharp.AE.exStrat_mem_comp_of_mem_exComp A.E A.q L hz⟩)
    (fun A hA L y σ hex => by
      obtain ⟨z, hz, hzout⟩ := hex
      exact Work.WilE9.Sharp.exSemiPf_snd_contDiff_gen hZS A.E (hGood A hA) A.comp (hQ A hA)
        (hπS A hA) L y σ ⟨z, Work.WilE9.Sharp.AE.exComp_subset_set A.E A.q L hz, hzout,
          Work.WilE9.Sharp.AE.exStrat_mem_comp_of_mem_exComp A.E A.q L hz⟩)
    (fun y hy L L' hp => Work.Sharp.glDeriv_perm hy hp)
  have hsec : Work.WilE9.Sharp.SecSpec n k S f := (hspec k).1
  have hlim : Work.WilE9.Sharp.LimSpec n k S f := (hspec k).2
  have hperm' : ∀ (L L' : List (Fin n)), L.length ≤ k → L'.length ≤ k → List.Perm L L' →
      Work.WilE9.Sharp.Eset n S L = Work.WilE9.Sharp.Eset n S L' :=
    fun L L' _ _ hp => hperm L L' hp
  have hDom : WilkiesDesign.E.Gen aD
      (MvPolynomial.eval ![D, b₁.eval D, k, a₁] bD) n
      (Work.WilE9.Sharp.DomSet2 n k S (WilkiesDesign.graphOf f)) :=
    hDomGen D k f S (b₁.eval D) hgr hlenS hfmtS hdegS hblS
  have hEset : WilkiesDesign.E.Gen aE
      (MvPolynomial.eval ![b₁.eval D, k, a₁] bE) (n + 1)
      (Work.WilE9.Sharp.Eset n S (List.ofFn v)) := by
    simpa only [List.length_ofFn] using
      hEsetGen (List.ofFn v) S (b₁.eval D) hlenS hfmtS hdegS hblS
  have hLift := WilkiesDesign.E.Gen.prod_right hDom
  have hInter := Work.WilE9.Gen.inter₂ hLift hEset
  rw [← Work.WilE9.Sharp.sdSet2_eq hsec hlim hperm' v] at hInter
  exact Work.WilE9.Gen.mono (le_refl _) (hb' D k) hInter

/-- The E instance: WilE8's `genSOMin` with E9's sharp derivatives. -/
theorem E_instance' (hP9 : Work.WilE7.Prop9) : ∃ S : SOMin, S.SharpCD ∧ S.SharpDeriv ∧
    ∀ N d : ℕ, ∃ F D : ℕ, ∀ (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ),
      P.totalDegree ≤ d → boxZero M P ∈ S.Ω F D N := by
  have hCompl := E.E7_star_compl_proved hP9
  have hInter := E.E7_star_inter_proved hP9
  have hE2 := Work.WilE2.E2_components_proved
  have hK : ∀ F, Work.WilE3.SepKhovanskiiET F :=
    Work.WilE3K.SepKhovanskiiET_of_E2 Work.WilE2.E2_khovanskii_proved
      (fun m G hG y₀ ε hε => Work.WilE2.regular_values_dense G hG y₀ ε hε)
  have hE5 := Work.WilE5.E5_strat_proved (Work.WilE3.E3_identity_proved hK) hE2
  have hEff := Work.WilE9G.EffStratAE_of_frozen hE2 hE5
  have hE8 := Work.WilE8.E8_reduce_proved hCompl hInter hE2
  have hGen : Work.WilE9.SharpDerivGen := sharpDerivGen_direct hE2 hEff hE8
  refine ⟨Work.WilE8.genSOMin hCompl hInter hE2,
    Work.WilE8.E8_sharpCD_proved hCompl hInter hE2 (E.E7_bv_main_proved hP9), ?_,
    Work.WilE8.E8_boxZero_proved hCompl hInter hE2⟩
  exact hGen

/-! ## C side -/

theorem curveSel_all : ∀ n, C4a.CurveSel n := fun n =>
  Nat.rec C4a.CurveSel_zero
    (fun k ih => C4a.C4a_CS_step_proved C4a.C4a_RW_proved
      (Work.WilC4aAL.C4a_arcLift_proved C4a.C4a_puiseux_proved) Work.WilC4aTS.C4a_TS1_proved k ih) n

theorem polyBounded' (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hUF : UnifFiniteRExp) : PolyBoundedRExp :=
  Work.WilC4aU.C4a_uniform_proved hR hUF fun _ Y hY hfun c =>
    Work.WilC4aA.C4a_asym_proved curveSel_all Y c (hfun c) (Work.WilC4aL.C4a_lift_proved Y hY c)

theorem C_wilkie_complement' (hP9 : Work.WilE7.Prop9)
    {n : ℕ} (X : Set (Fin n → ℝ)) (h : ExpExist X) : ExpExist Xᶜ := by
  have hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ :=
    fun n Y hY => E0_rexp_complement' hP9 Y hY
  have hUF : UnifFiniteRExp := E0b_unif_finite_proved hP9
    (Work.WilE8.E8_comps_proved (E.E7_star_compl_proved hP9) (E.E7_star_inter_proved hP9)
      Work.WilE2.E2_components_proved)
  have hPB := polyBounded' hR hUF
  have hOM : OMinModels :=
    Work.WilC2.C2_models_ominimal_proved hR (fun n Y hY => C0_rexp_syntax_proved hR Y hY) hUF
  exact C6_compl_of_modelComplete_proved
    (C5_TE_modelComplete_proved (C1_TR_modelComplete_proved hR) hOM
      (C4_valuation_inequality_proved hR hOM hPB) (Work.WilVP.ValProp_TR hR hOM hPB)) X h

/-! ## G side (with the corrected `F1AffineW`) -/

theorem G_alg_lemma' (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (F n : ℕ) :
    AlgLemma S F n := by
  have h1 : ∀ p, Work.WilG4a.F1AffineW S p := fun p => (G4_base_proved_wired S hcd hder p).2
  have hchoice : Work.WilkG4c.ChoiceHyp S := G1_choice_proved S hcd
  have hbdd : Work.WilkG4c.BddDxHyp S := Work.WilG4b.G4_bdd_dx_proved S hcd hder hchoice
  have hF : ∀ n p, FLem S p n := by
    intro n
    induction n with
    | zero => exact fun p => WilkiesDesign.CG.G4_zero_proved S p
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; exact fun p => (G4_base_proved_wired S hcd hder p).1
      · exact Work.WilkG4c.G4_step_provedW S hcd hder n hpos h1 ih hchoice hbdd
  exact G5_alg_of_FLem_proved S hcd hder (fun p n => hF n p) F n

/-! ## Top -/

theorem corollary_1_of_prop9 (hP9 : Work.WilE7.Prop9) {n : ℕ} (X : Set (Fin n → ℝ))
    (h : IsRExpDefinable X) :
    ∃ f : MvPolynomial (Fin 2) ℝ, ∀ (g H : ℕ),
      Nat.card (degreeHeightLE X.trans g H) ≤ f.eval ![(g : ℝ), Real.log H] := by
  obtain ⟨S, hcd, hder, hbox⟩ := E_instance' hP9
  have hW : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), ExpExist X → ExpExist Xᶜ :=
    fun n X hX => C_wilkie_complement' hP9 X hX
  exact D_truncation S hbox (H_count S hcd hder (G_alg_lemma' S hcd hder)) X (B_syntax hW X h)

/-! ## E7 inputs and the unconditional top -/

/-- `Prop9` (= frozen `E.E7_prop_main`) from area E7's `E7_prop_main_proved` and the delivered
E2/E3/E4/E5/E6 + E7 fiber cut. Its only open input is `E7_prop_main_proved` itself. -/
theorem prop9_proved : Work.WilE7.Prop9 := by
  have hE2 := Work.WilE2.E2_components_proved
  have hK : ∀ F, Work.WilE3.SepKhovanskiiET F :=
    Work.WilE3K.SepKhovanskiiET_of_E2 Work.WilE2.E2_khovanskii_proved
      (fun m G hG y₀ ε hε => Work.WilE2.regular_values_dense G hG y₀ ε hε)
  have hE5 := Work.WilE5.E5_strat_proved (Work.WilE3.E3_identity_proved hK) hE2
  have hE6 := Work.WilE6.E6_fiber_closure_proved (Work.WilE3.E3_taylor_closure_proved_hK hK)
    Work.WilE4.E4_sa_fiber_closure_proved hE2
  have hFC := Work.WilE7.E7_fiber_cut_proved hE2 hE5 hE6
  exact Work.WilE7.E7_prop_main_proved hFC hE2 hE5 hE6

/-- **The Wilkies conjecture (frozen `WilkiesDesign.corollary_1` statement)**, fully composed.
Its only open leaf is area E7's `Work.WilE7.E7_prop_main_proved`. -/
theorem corollary_1_final {n : ℕ} (X : Set (Fin n → ℝ)) (h : IsRExpDefinable X) :
    ∃ f : MvPolynomial (Fin 2) ℝ, ∀ (g H : ℕ),
      Nat.card (degreeHeightLE X.trans g H) ≤ f.eval ![(g : ℝ), Real.log H] :=
  corollary_1_of_prop9 prop9_proved X h

end Work.WilFinal
