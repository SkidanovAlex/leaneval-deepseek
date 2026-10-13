/-
  WilC4aA : area C4aA of `annals_wilkies_conjecture` -- the analytic asymptotics step
  `C4a_asym` of area C4a (`Submission/Work/Wilkies/CG/C4a/Spec.lean`).

  MAIN RESULTS (all in namespace `Work.WilC4aA`):

  * `C4a_asym_proved` -- exactly the frozen hole `WilkiesDesign.CG.C4a.C4a_asym`:
    from curve selection in every dimension, a set `Y` whose slice at `c` is a finite union of
    good basic semianalytic pieces over `t = 1/x > 0` and is the graph of a function of `x`,
    conclude `PBOne Y c`.  The same statement is also exported as
    `WilkiesDesign.CG.C4a.C4a_asym_proved`.

  * `pbOne_first_of_noaccum` and `pbOne_of_arc` -- the two halves of the proof (the slice is
    eventually empty, resp. the asymptotics along an analytic arc in an accumulating piece).

  SUPPORTING API (`Submission.Work.WilC4aA.Defs`, imported by everything below):

  * `Accum P`      : the piece `P` has points with `t`-coordinate arbitrarily close to `0⁺`.
  * `HasAsymAt0 f`: one-sided asymptotics at `0⁺` with an integer exponent; equivalently `f` is
                    `~ b s^k` (`k : ℤ`, `b ≠ 0`) or vanishes identically near `0⁺`.
  * `arcVal P γ`   : the `y`-value represented by the point `γ s` of the piece `P`.

  Lemmas proved in the sibling modules of this directory (each imported below):
  `accum_closure_point` (D1), `analytic_hasAsymAt0` (D2), `hasAsymAt0_inv` (D3),
  `analytic_factor` (D4), `asym_div_rpow` (D5), `rep_arcVal` (D6), `hasAsymAt0_arcVal` (D7),
  `exists_delta_of_not_accum` (D8), `analyticAt_exists_continuousOn` (D9).

  A caller only needs `import Submission.Work.WilC4aA.Main`.
-/
import Submission.Work.WilC4aA.Defs
import Submission.Work.WilC4aA.accum_closure_point
import Submission.Work.WilC4aA.analytic_hasAsymAt0
import Submission.Work.WilC4aA.hasAsymAt0_inv
import Submission.Work.WilC4aA.analytic_factor
import Submission.Work.WilC4aA.asym_div_rpow
import Submission.Work.WilC4aA.rep_arcVal
import Submission.Work.WilC4aA.hasAsymAt0_arcVal
import Submission.Work.WilC4aA.exists_delta_of_not_accum
import Submission.Work.WilC4aA.analyticAt_exists_continuousOn
import Submission.Work.WilC4aA.asymT_of_arc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology Filter Set
namespace Work.WilC4aA

open WilkiesDesign WilkiesDesign.CG WilkiesDesign.CG.C4a

/-! ## 1. The non-accumulating case: the slice is eventually empty. -/

theorem pbOne_first_of_noaccum {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ}
    (L : List LiftPiece)
    (hdesc : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ y : ℝ,
      (Fin.cons t⁻¹ (Fin.cons y c) ∈ Y ↔ ∃ P ∈ L, ∃ z ∈ P.set, z 0 = t ∧ P.Rep z y))
    (h : ∀ P ∈ L, ¬ Accum P) :
    ∃ R : ℝ, ∀ x y : ℝ, R ≤ x → Fin.cons x (Fin.cons y c) ∈ Y → y = 0 := by
  obtain ⟨δ, hδ, hbdd⟩ := exists_delta_of_not_accum L h
  refine ⟨δ⁻¹ + 1, fun x y hx hpt => ?_⟩
  have hx0 : (0 : ℝ) < x := by
    have h1 : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδ
    linarith
  have hxd : δ⁻¹ < x := by linarith
  have hxinv_lt : x⁻¹ < δ := by
    have h1 := (inv_lt_inv₀ hx0 (inv_pos.mpr hδ)).mpr hxd
    rwa [inv_inv] at h1
  have hxinv_lt_one : x⁻¹ < 1 := by
    refine inv_lt_one_of_one_lt₀ ?_
    have h1 : (0 : ℝ) < δ⁻¹ := inv_pos.mpr hδ
    linarith
  obtain ⟨P, hP, z, hz, hz0, _⟩ :=
    (hdesc x⁻¹ ⟨inv_pos.mpr hx0, hxinv_lt_one⟩ y).mp (by simpa using hpt)
  have hzmem : z 0 ∈ Set.Ioo (0 : ℝ) δ := by
    rw [hz0]
    exact ⟨inv_pos.mpr hx0, hxinv_lt⟩
  exact absurd hzmem (hbdd P hP z hz)

/-! ## 2. The arc case: the asymptotics along the arc give the second disjunct. -/

theorem pbOne_of_arc {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {c : Fin k → ℝ}
    (L : List LiftPiece)
    (hdesc : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ y : ℝ,
      (Fin.cons t⁻¹ (Fin.cons y c) ∈ Y ↔ ∃ P ∈ L, ∃ z ∈ P.set, z 0 = t ∧ P.Rep z y))
    (hfun : ∀ x y y' : ℝ, Fin.cons x (Fin.cons y c) ∈ Y →
      Fin.cons x (Fin.cons y' c) ∈ Y → y = y')
    {P : LiftPiece} (hP : P ∈ L) (hPg : P.Good)
    {γ : ℝ → Fin (P.m + 2) → ℝ} (hγan : AnalyticAt ℝ γ 0) (hγ0 : (γ 0) 0 = 0)
    (hγmem : ∀ᶠ s in 𝓝[>] (0 : ℝ), γ s ∈ P.set)
    (hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < (γ s) 0) :
    PBOne Y c := by
  have htan : AnalyticAt ℝ (fun s : ℝ => (γ s) 0) 0 := by
    have h := ((ContinuousLinearMap.proj (0 : Fin (P.m + 2))).analyticAt (γ 0)).comp hγan
    simpa [Function.comp_def] using h
  have ht0 : (fun s : ℝ => (γ s) 0) 0 = 0 := hγ0
  obtain ⟨N, u, hN, hu, hu0, _hupos, htu⟩ := analytic_factor htan ht0 hpos
  obtain ⟨_htpos, hcases⟩ := asym_div_rpow hN hu hu0 htu (hasAsymAt0_arcVal hPg hγan hγmem)
  have hrepev : ∀ᶠ s in 𝓝[>] (0 : ℝ), P.Rep (γ s) (arcVal P γ s) := rep_arcVal hPg hγmem
  obtain ⟨εm, hεm, hm⟩ := eventually_nhdsGT_iff.mp hγmem
  obtain ⟨εr, hεr, hr⟩ := eventually_nhdsGT_iff.mp hrepev
  obtain ⟨εp, hεp, hp⟩ := eventually_nhdsGT_iff.mp hpos
  have glue : ∀ {ε : ℝ}, 0 < ε → (∀ s ∈ Set.Ioo (0 : ℝ) ε, γ s ∈ P.set) →
      (∀ s ∈ Set.Ioo (0 : ℝ) ε, P.Rep (γ s) (arcVal P γ s)) → 0 < (γ (ε / 2)) 0 →
      ContinuousOn (fun s : ℝ => (γ s) 0) (Set.Icc 0 (ε / 2)) →
      ∃ η > (0 : ℝ), ∀ t' ∈ Set.Ioo (0 : ℝ) η, ∃ s ∈ Set.Ioo (0 : ℝ) ε, (γ s) 0 = t' ∧
        ∀ y : ℝ, Fin.cons t'⁻¹ (Fin.cons y c) ∈ Y → y = arcVal P γ s := by
    intro ε hε hmemε hrepε hposε hcontε
    refine ⟨min ((γ (ε / 2)) 0) (1 / 2), lt_min hposε (by linarith : (0 : ℝ) < 1 / 2), ?_⟩
    intro t' ht'
    obtain ⟨ht'pos, ht'ltη⟩ := ht'
    have ht'lt1 : t' < 1 :=
      lt_of_lt_of_le ht'ltη (le_trans (min_le_right ((γ (ε / 2)) 0) (1 / 2)) (by linarith : (1 : ℝ) / 2 ≤ 1))
    have hmemI : t' ∈ Set.Icc ((fun s : ℝ => (γ s) 0) 0) ((fun s : ℝ => (γ s) 0) (ε / 2)) :=
      ⟨by rw [ht0]; exact ht'pos.le,
        le_of_lt (lt_of_lt_of_le ht'ltη (min_le_left ((γ (ε / 2)) 0) (1 / 2)))⟩
    obtain ⟨s₀, hs₀Icc, hs₀eq⟩ :=
      intermediate_value_Icc (by linarith : (0 : ℝ) ≤ ε / 2) hcontε hmemI
    have hs₀ne : s₀ ≠ 0 := by
      intro h0
      have h1 : (0 : ℝ) = t' := by rw [← hs₀eq, h0, ht0]
      exact absurd h1.symm (ne_of_gt ht'pos)
    have hs₀mem : s₀ ∈ Set.Ioo (0 : ℝ) ε :=
      ⟨lt_of_le_of_ne hs₀Icc.1 (Ne.symm hs₀ne), lt_of_le_of_lt hs₀Icc.2 (by linarith)⟩
    refine ⟨s₀, hs₀mem, hs₀eq, fun y hy => ?_⟩
    have harc : Fin.cons t'⁻¹ (Fin.cons (arcVal P γ s₀) c) ∈ Y :=
      (hdesc t' ⟨ht'pos, ht'lt1⟩ (arcVal P γ s₀)).mpr
        ⟨P, hP, γ s₀, hmemε s₀ hs₀mem, hs₀eq, hrepε s₀ hs₀mem⟩
    exact (hfun t'⁻¹ (arcVal P γ s₀) y harc hy).symm
  obtain ⟨rt, hrt, hcontt⟩ := analyticAt_exists_continuousOn htan
  rcases hcases with hzero | ⟨q, b, hb, hlim⟩
  · refine Or.inl ?_
    obtain ⟨εz, hεz, hz⟩ := eventually_nhdsGT_iff.mp hzero
    set ε : ℝ := min εz (min εm (min εr (min εp rt))) with hεdef
    have hε : 0 < ε := lt_min hεz (lt_min hεm (lt_min hεr (lt_min hεp hrt)))
    have hεle_z : ε ≤ εz := by rw [hεdef]; exact min_le_left _ _
    have hεle_m : ε ≤ εm := by
      rw [hεdef]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hεle_r : ε ≤ εr := by
      rw [hεdef]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hεle_p : ε ≤ εp := by
      rw [hεdef]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _)))
    have hεle_t : ε ≤ rt := by
      rw [hεdef]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_right _ _)))
    have hcontε : ContinuousOn (fun s : ℝ => (γ s) 0) (Set.Icc 0 (ε / 2)) :=
      hcontt.mono (fun s hs => ⟨by linarith [hs.1, hrt], lt_of_le_of_lt hs.2 (by linarith)⟩)
    obtain ⟨η, hηpos, hglue⟩ := glue hε
      (fun s hs => hm s ⟨hs.1, lt_of_lt_of_le hs.2 hεle_m⟩)
      (fun s hs => hr s ⟨hs.1, lt_of_lt_of_le hs.2 hεle_r⟩)
      (hp (ε / 2) ⟨by linarith, lt_of_lt_of_le (by linarith) hεle_p⟩) hcontε
    refine ⟨η⁻¹ + 1, fun x y hx hpt => ?_⟩
    have hx0 : (0 : ℝ) < x := by
      have h1 : (0 : ℝ) < η⁻¹ + 1 := by positivity
      linarith
    have hxin : x⁻¹ < η := by
      have h1 : x⁻¹ < (η⁻¹)⁻¹ := (inv_lt_inv₀ hx0 (inv_pos.mpr hηpos)).mpr (by linarith)
      rwa [inv_inv] at h1
    obtain ⟨s₀, hs₀, hs₀eq, hval⟩ := hglue x⁻¹ ⟨inv_pos.mpr hx0, hxin⟩
    have hyv : y = arcVal P γ s₀ := hval y (by simpa using hpt)
    have hz₀ : arcVal P γ s₀ = 0 := hz s₀ ⟨hs₀.1, lt_of_lt_of_le hs₀.2 hεle_z⟩
    rw [hyv, hz₀]
  · refine Or.inr ⟨-q, b, hb, fun ε' hε' => ?_⟩
    obtain ⟨εb, hεb, hbnd⟩ :=
      eventually_nhdsGT_iff.mp ((Metric.tendsto_nhds.mp hlim) ε' hε')
    set ε : ℝ := min εb (min εm (min εr (min εp rt))) with hεdef
    have hε : 0 < ε := lt_min hεb (lt_min hεm (lt_min hεr (lt_min hεp hrt)))
    have hεle_b : ε ≤ εb := by rw [hεdef]; exact min_le_left _ _
    have hεle_m : ε ≤ εm := by
      rw [hεdef]
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hεle_r : ε ≤ εr := by
      rw [hεdef]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hεle_p : ε ≤ εp := by
      rw [hεdef]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _)))
    have hεle_t : ε ≤ rt := by
      rw [hεdef]
      exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_right _ _)))
    have hcontε : ContinuousOn (fun s : ℝ => (γ s) 0) (Set.Icc 0 (ε / 2)) :=
      hcontt.mono (fun s hs => ⟨by linarith [hs.1, hrt], lt_of_le_of_lt hs.2 (by linarith)⟩)
    obtain ⟨η, hηpos, hglue⟩ := glue hε
      (fun s hs => hm s ⟨hs.1, lt_of_lt_of_le hs.2 hεle_m⟩)
      (fun s hs => hr s ⟨hs.1, lt_of_lt_of_le hs.2 hεle_r⟩)
      (hp (ε / 2) ⟨by linarith, lt_of_lt_of_le (by linarith) hεle_p⟩) hcontε
    refine ⟨η⁻¹ + 1, fun x y hx hpt => ?_⟩
    have hx0 : (0 : ℝ) < x := by
      have h1 : (0 : ℝ) < η⁻¹ + 1 := by positivity
      linarith
    have hxin : x⁻¹ < η := by
      have h1 : x⁻¹ < (η⁻¹)⁻¹ := (inv_lt_inv₀ hx0 (inv_pos.mpr hηpos)).mpr (by linarith)
      rwa [inv_inv] at h1
    obtain ⟨s₀, hs₀, hs₀eq, hval⟩ := hglue x⁻¹ ⟨inv_pos.mpr hx0, hxin⟩
    have hyv : y = arcVal P γ s₀ := hval y (by simpa using hpt)
    have hbnd₀ : dist (arcVal P γ s₀ / ((γ s₀) 0) ^ ((q : ℝ))) b < ε' :=
      hbnd s₀ ⟨hs₀.1, lt_of_lt_of_le hs₀.2 hεle_b⟩
    have hrpow : x ^ (((-q : ℚ) : ℝ)) = (x⁻¹) ^ ((q : ℚ) : ℝ) := by
      have hcast : (((-q : ℚ) : ℝ)) = -(((q : ℚ) : ℝ)) := by simp
      rw [hcast]
      calc x ^ (-(((q : ℚ) : ℝ))) = (x ^ (((q : ℚ) : ℝ)))⁻¹ := Real.rpow_neg hx0.le _
        _ = (x⁻¹) ^ (((q : ℚ) : ℝ)) := (Real.inv_rpow hx0.le _).symm
    rw [hyv, hrpow, ← hs₀eq]
    simpa [Real.dist_eq] using hbnd₀

/-! ## 3. The frozen hole `C4a_asym`. -/

/-- **`C4a_asym`**: an analytic arc in a piece, whose value function has one-sided
asymptotics, produces the polynomial bound with rational exponent at every slice point. -/
theorem C4a_asym_proved (hCS : ∀ n, CurveSel n) {k : ℕ} (Y : Set (Fin (k + 2) → ℝ))
    (c : Fin k → ℝ)
    (hfun : ∀ x y y' : ℝ, Fin.cons x (Fin.cons y c) ∈ Y →
      Fin.cons x (Fin.cons y' c) ∈ Y → y = y')
    (hL : SliceLift Y c) : PBOne Y c := by
  obtain ⟨L, hGood, hdesc⟩ := hL
  by_cases hacc : ∃ P ∈ L, Accum P
  · obtain ⟨P, hP, haccP⟩ := hacc
    obtain ⟨q, hqcl, hq0⟩ := accum_closure_point (good_isBounded (hGood P hP)) haccP
    obtain ⟨γ, hγan, hγ0, ε, hεpos, hγε⟩ :=
      hCS (P.m + 2) P.l P.F P.g q (good_anF (hGood P hP) q)
        (fun j => good_ang (hGood P hP) j q) (by simpa [LiftPiece.set_eq_BasicSA] using hqcl)
    refine pbOne_of_arc L hdesc hfun hP (hGood P hP) hγan ?_ ?_ ?_
    · rw [hγ0]; exact hq0
    · exact eventually_nhdsGT_of_forall_Ioo hεpos (fun s hs => hγε s hs)
    · exact eventually_nhdsGT_of_forall_Ioo hεpos
        (fun s hs => good_pos (hGood P hP) (γ s) (hγε s hs))
  · exact Or.inl (pbOne_first_of_noaccum L hdesc (fun P hP haccP => hacc ⟨P, hP, haccP⟩))

end Work.WilC4aA

namespace WilkiesDesign.CG.C4a

/-- `C4a_asym_proved`, in the namespace of the frozen hole. -/
theorem C4a_asym_proved (hCS : ∀ n, CurveSel n) {k : ℕ} (Y : Set (Fin (k + 2) → ℝ))
    (c : Fin k → ℝ)
    (hfun : ∀ x y y' : ℝ, Fin.cons x (Fin.cons y c) ∈ Y →
      Fin.cons x (Fin.cons y' c) ∈ Y → y = y')
    (hL : SliceLift Y c) : PBOne Y c :=
  Work.WilC4aA.C4a_asym_proved hCS Y c hfun hL

end WilkiesDesign.CG.C4a

namespace Work.WilC4aA

open WilkiesDesign.CG.C4a

set_option linter.unusedVariables false

/-! ## 4. Comparison with the frozen hole. -/

/-- `C4a_asym_proved` has exactly the type of the frozen hole `C4a_asym`. -/
example : (∀ (hCS : ∀ n, CurveSel n) {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ)
    (hfun : ∀ x y y' : ℝ, Fin.cons x (Fin.cons y c) ∈ Y → Fin.cons x (Fin.cons y' c) ∈ Y →
      y = y')
    (hL : SliceLift Y c), PBOne Y c) :=
  @Work.WilC4aA.C4a_asym_proved

/-- The frozen hole has the same statement. -/
example : (∀ (hCS : ∀ n, CurveSel n) {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ)
    (hfun : ∀ x y y' : ℝ, Fin.cons x (Fin.cons y c) ∈ Y → Fin.cons x (Fin.cons y' c) ∈ Y →
      y = y')
    (hL : SliceLift Y c), PBOne Y c) :=
  @WilkiesDesign.CG.C4a.C4a_asym

end Work.WilC4aA
