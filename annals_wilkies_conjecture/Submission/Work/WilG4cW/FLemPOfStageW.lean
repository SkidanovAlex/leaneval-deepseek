import Mathlib
import Submission.Work.WilG4cW.StepStageW
import Submission.Work.WilG4cW.ChartW
import Submission.Work.WilG4cW.SubdivChartW
import Submission.Work.WilG4c.FLemPOfStage

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4cW

/-
  NB: the harness requires the declared name to equal the file's last segment, so this
  declaration is at the ROOT of the namespace tree, named `FLemPOfStageW` (do not wrap it in a
  `namespace`).  File `Submission/Work/WilG4cW/FLemPOfStageW.lean`, module
  `Submission.Work.WilG4cW.FLemPOfStageW`.

  ROUTE: verbatim copy of the PROVED `Work.WilkG4c.FLemP_of_stage`
  (`Submission/Work/WilG4c/FLemPOfStage.lean`) with the stage hypothesis `Work.WilkG4c.StepStage`
  replaced by `Work.WilkG4c.StepStageW` (`Submission/Work/WilG4cW/StepStageW.lean`).
  `StepStageW` differs from `StepStage` only in the per-chart condition:
  `0 < cb.2 l ∧ 0 ≤ cb.1 l ∧ cb.1 l + cb.2 l ≤ 1` becomes `Work.WilkG4c.ChartInW cb.1 cb.2`,
  i.e. `∀ l, 0 ≤ β l ∧ 0 ≤ α l ∧ α l + β l ≤ 1 ∧ ∀ t ∈ I, α l + β l * t ∈ I`.
  INTENDED PROOF: copy `FLemP_of_stage`'s proof verbatim, with these changes (all inside the
  per-chart data `hdata` and in the final `ChartsOK`/`Covers` blocks):
   * extract from `((hΦ₁ok cb hcb).2.2 l)` the four components `.1 : 0 ≤ cb.2 l`,
     `.2.1 : 0 ≤ cb.1 l`, `.2.2.1 : cb.1 l + cb.2 l ≤ 1`,
     `.2.2.2 : ∀ t ∈ I, cb.1 l + cb.2 l * t ∈ I`;
   * use the PROVED W-variants instead of the originals: `Work.WilkG4c.pullX_YBoundW`,
     `Work.WilkG4c.pullX_lipW`, `Work.WilkG4c.valuesIn01_pullXW`
     (`Submission/Work/WilG4cW/ChartW.lean`, each taking the single chart hypothesis
     `Work.WilkG4c.ChartInW α β`), and `Work.WilkG4c.subdivChart_mem_openCubeW`,
     `Work.WilkG4c.covers_subdivChartW` (`Submission/Work/WilG4cW/SubdivChartW.lean`, the last
     one with hypothesis `∀ cb ∈ Φ₁, ChartInW cb.1 cb.2` instead of
     `∀ cb ∈ Φ₁, ∀ l, 0 < cb.2 l ∧ …`).
   Nothing else changes: `Work.WilkG4c.pullback_pylipdef_multi_badBC` consumes only `CurveData`,
   `YBound` and `LipOnCube` of the pullback, `famGraph_pullX` and `subdivChart_graph_mem` are
   chart-condition free, and the counting argument is untouched.
-/

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c

theorem FLemPOfStageW (S : WilkiesDesign.SOMin) (n p : ℕ) (hn : 1 ≤ n)
    (hStage : Work.WilkG4c.StepStageW S p n)
    (hP2 : Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLipDef p n)) :
    Work.WilkG4c.FLemP S p (n + 1) (Work.WilkG4c.PYLip p n) := by
  classical
  obtain ⟨Kpull, hPull⟩ := Work.WilG4c.famGraph_pullX S p n
  obtain ⟨K₁, hK₁⟩ := famGraph_subdivMap_mem S p n
  obtain ⟨A, C, hSub⟩ := Work.WilkG4c.subdivChart_graph_mem S p n
  obtain ⟨K₀, hK₀⟩ := Work.WilG4c.subdivN_le n
  intro F0
  obtain ⟨a₁, b₁, c, hstc⟩ := hStage F0
  obtain ⟨a₂, b₂, c₂, hhP2⟩ :=
    (FLemP_iff S p (n + 1) (PYLipDef p n)).mp hP2 (F0 + a₁ + Kpull + K₁)
  -- the count polynomial of the general branch, composed with the degree substitution `Dg`
  obtain ⟨c₂', hc₂'⟩ := Work.WilG4c.polyCountEval_comp4
    (MvPolynomial.X 0 + 2 * b₁) (Kpull + 2) c₂
  -- the degree substitution `X₀ ↦ X₀ + 2 b₁ + (Kpull+2)` for the `hP2`-degree `b₂`
  set b₂s : MvPolynomial (Fin 2) ℕ := MvPolynomial.eval₂ MvPolynomial.C
    ![(MvPolynomial.X 0 + 2 * b₁ + MvPolynomial.C (Kpull + 2)), MvPolynomial.X 1] b₂ with hb₂s
  set bge : MvPolynomial (Fin 2) ℕ :=
    MvPolynomial.C C * (b₁ + b₂s) + MvPolynomial.C C with hbge
  -- the count polynomial of the `r = 0` branch
  set cA : MvPolynomial (Fin 4) ℝ := MvPolynomial.eval₂ MvPolynomial.C
    (fun i : Fin 4 => if i = 0 then MvPolynomial.X 0
      else if i = 1 then MvPolynomial.C (0 : ℝ) else MvPolynomial.X i) c₂ with hcA
  -- the count polynomial of the general branch
  set cB : MvPolynomial (Fin 4) ℝ := c * MvPolynomial.C (((3 * K₀ + 4) ^ (n + 1) : ℕ) : ℝ)
    * (MvPolynomial.X 1 + MvPolynomial.C 1) ^ (n + 1) * c₂' with hcB
  refine ⟨a₁ + a₂ + A + a₂, bge + b₂, 1 + cA ^ 2 + cB ^ 2, ?_⟩
  intro D r k ε hε hε1 Λ F hP hΩ hval
  have hcev := eval_one_add_sq_add_sq cA cB ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε]
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · -- ## the case `r = 0`: `PYLip` and `PYLipDef` coincide, so `hP2` applies to `F` itself
    subst hr0
    have hPD : PYLipDef p n 0 k F := Work.WilG4c.pylipDef_zero_of_pylip hP
    obtain ⟨Ψ, hΨcard, hΨok, hΨcov⟩ := hhP2 D 0 k ε hε hε1 Λ F hPD
      (fun i => Omega_mono_le S (by omega) le_rfl (hΩ i)) hval
    have hce : ∀ z : ℝ, MvPolynomial.eval ![(D : ℝ), z, (k : ℝ), -Real.log ε] cA
        = MvPolynomial.eval ![(D : ℝ), ((0 : ℕ) : ℝ), (k : ℝ), -Real.log ε] c₂ := by
      intro z
      rw [hcA, eval_eval₂_C_real]
      rw [show (fun s : Fin 4 => MvPolynomial.eval ![(D : ℝ), z, (k : ℝ), -Real.log ε]
            (if s = 0 then MvPolynomial.X 0
              else if s = 1 then MvPolynomial.C (0 : ℝ) else MvPolynomial.X s))
          = ![(D : ℝ), ((0 : ℕ) : ℝ), (k : ℝ), -Real.log ε] from by
        funext i
        fin_cases i <;> simp]
    refine ⟨Ψ, ?_, ?_, ?_⟩
    · rw [hcev, hce]
      exact le_trans hΨcard (le_one_add_sq_add_sq _ _)
    · refine ChartsOK_mono_stage hΨok (by omega) ?_
      show MvPolynomial.eval ![D, 0] b₂ ≤ MvPolynomial.eval ![D, 0] (bge + b₂)
      rw [MvPolynomial.eval_add, hbge]
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
      exact Nat.le_add_left _ _
    · exact hΨcov
  · -- ## the general case `r ≥ 1`
    have hr1 : 1 ≤ r := hrpos
    obtain ⟨Φ₁, hΦ₁card, hΦ₁ok, hΦ₁cov, hΦ₁curve⟩ := hstc D r k ε hr1 hε hε1 Λ F hP hΩ hval
    have hNpos : 1 ≤ subdivN n r := Work.WilkG4c.subdivN_pos hr1
    by_cases hΛ : Λ = ∅
    · -- the parameter set is empty: the empty chart family already satisfies everything
      refine ⟨∅, ?_, ?_, ?_⟩
      · rw [Finset.card_empty]
        push_cast
        rw [hcev]
        nlinarith [sq_nonneg (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA),
          sq_nonneg (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cB)]
      · intro φ hφ
        exact absurd hφ (Finset.notMem_empty φ)
      · intro l hl
        rw [hΛ] at hl
        exact absurd hl (Set.notMem_empty l)
    · obtain ⟨l₀, hl₀⟩ := Set.nonempty_iff_ne_empty.mpr hΛ
      -- the subdivision index type is nonempty, and `Λ ≠ ∅` forces `Φ₁ ≠ ∅`
      have hsne : Nonempty (Fin (n + 1) → Fin (3 * (subdivN n r - 1) + 1)) :=
        ⟨fun _ => ⟨0, by omega⟩⟩
      obtain ⟨s₀⟩ := hsne
      have hΦ₁ne : Φ₁.Nonempty := by
        obtain ⟨cb, hcb, -⟩ := hΦ₁cov l₀ hl₀ (1 / 2) (by norm_num [I])
        exact ⟨cb, hcb⟩
      obtain ⟨cb₀, hcb₀⟩ := hΦ₁ne
      -- the format and degree of the subdivided pullback graphs, and the composed count
      set Dg : ℕ := D + 2 * MvPolynomial.eval ![D, r] b₁ + Kpull + 2 with hDg
      set c₂ev : ℝ := MvPolynomial.eval ![(Dg : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] c₂
        with hc₂evdef
      -- the `hP2`-chart family of every subdivided pullback
      have hdata : ∀ (cb : ((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ))
          (s : Fin (n + 1) → Fin (3 * (subdivN n r - 1) + 1)), cb ∈ Φ₁ →
          ∃ Ψ : Finset (ChartTuple p (n + 1)),
            ((Ψ.card : ℝ) ≤ c₂ev) ∧
            ChartsOK S a₂ (MvPolynomial.eval ![Dg, r] b₂) r Λ (subdivFam F cb.1 cb.2 s) Ψ ∧
            Covers Λ (subdivFam F cb.1 cb.2 s) Ψ (ε / 2) := by
        intro cb s hcb
        have hcW : ChartInW cb.1 cb.2 := (hΦ₁ok cb hcb).2.2
        have hα : ∀ l, 0 ≤ cb.1 l := fun l => (hcW l).2.1
        have hβ : ∀ l, 0 ≤ cb.2 l := fun l => (hcW l).1
        have hY : YBound (pullX F cb.1 cb.2) r :=
          Work.WilkG4c.pullX_YBoundW hP.1 hcW
        have hL : LipOnCube (pullX F cb.1 cb.2) 1 :=
          Work.WilkG4c.pullX_lipW hP.2 hcW
        have hPD : PYLipDef p n r k (subdivFam F cb.1 cb.2 s) :=
          Work.WilG4c.pullback_pylipdef_multi_badBC hr1 (pullX F cb.1 cb.2) s hY hL
            (hΦ₁curve cb hcb)
        have hval' : ValuesIn01 Λ (pullX F cb.1 cb.2) :=
          Work.WilkG4c.valuesIn01_pullXW hval hcW
        have hvalG : ValuesIn01 Λ (subdivFam F cb.1 cb.2 s) :=
          valuesIn01_subdivMap hNpos s hval'
        have hΩG : ∀ i, famGraph (subdivFam F cb.1 cb.2 s i) ∈
            S.Ω (F0 + a₁ + Kpull + K₁) Dg (p + (n + 1) + 1) := by
          intro i
          have h1 := hPull a₁ (MvPolynomial.eval ![D, r] b₁) F0 D cb.1 cb.2 (F i)
            (hΦ₁ok cb hcb).1 (hΦ₁ok cb hcb).2.1 (hΩ i)
          have h2 := hK₁ (subdivN n r) s (F0 + a₁ + Kpull)
            (D + 2 * MvPolynomial.eval ![D, r] b₁ + Kpull) (pullX F cb.1 cb.2 i) h1
          rw [hDg]
          exact h2
        obtain ⟨Ψ, hΨ1, hΨ2, hΨ3⟩ :=
          hhP2 Dg r k (ε / 2) (by linarith) (by linarith) Λ (subdivFam F cb.1 cb.2 s)
            hPD hΩG hvalG
        exact ⟨Ψ, by rw [hc₂evdef]; exact hΨ1, hΨ2, hΨ3⟩
      set Ψ : (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)) →
          (Fin (n + 1) → Fin (3 * (subdivN n r - 1) + 1)) →
          Finset (ChartTuple p (n + 1)) :=
        fun cb s => if h : cb ∈ Φ₁ then (hdata cb s h).choose else ∅ with hΨ
      have hΨspec : ∀ cb (hcb : cb ∈ Φ₁) s, ((Ψ cb s).card : ℝ) ≤ c₂ev ∧
          ChartsOK S a₂ (MvPolynomial.eval ![Dg, r] b₂) r Λ (subdivFam F cb.1 cb.2 s) (Ψ cb s) ∧
          Covers Λ (subdivFam F cb.1 cb.2 s) (Ψ cb s) (ε / 2) := by
        intro cb hcb s
        have hΨeq : Ψ cb s = (hdata cb s hcb).choose := by
          rw [hΨ]
          show (if h : cb ∈ Φ₁ then (hdata cb s h).choose else ∅) = (hdata cb s hcb).choose
          rw [dif_pos hcb]
        rw [hΨeq]
        exact (hdata cb s hcb).choose_spec
      -- the composed count is nonnegative (it dominates a cardinality)
      have hc₂evnn : 0 ≤ c₂ev :=
        le_trans (Nat.cast_nonneg _) (hΨspec cb₀ hcb₀ s₀).1
      have hc₁nn : 0 ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c :=
        le_trans (Nat.cast_nonneg _) hΦ₁card
      -- ## the cardinality of the final chart family
      have hKsub : (3 * (subdivN n r - 1) + 1) ^ (n + 1)
          ≤ ((3 * K₀ + 4) * (r + 1)) ^ (n + 1) := by
        refine Nat.pow_le_pow_left ?_ _
        have h1 : 3 * (subdivN n r - 1) + 1 ≤ 3 * subdivN n r + 1 := by omega
        have h2 : 3 * subdivN n r + 1 ≤ 3 * (K₀ * r + 1) + 1 := by
          have := hK₀ r; omega
        have h3 : 3 * (K₀ * r + 1) + 1 ≤ (3 * K₀ + 4) * (r + 1) := by
          nlinarith [Nat.zero_le r, Nat.zero_le K₀, Nat.zero_le (K₀ * r)]
        omega
      have hcard : ((Φ₁.biUnion (fun cb => Finset.univ.biUnion (fun s =>
            (Ψ cb s).image (fun ψ => subdivChart cb.1 cb.2 s ψ)))).card : ℝ)
          ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cB := by
        have h1 : ((Φ₁.biUnion (fun cb => Finset.univ.biUnion (fun s =>
              (Ψ cb s).image (fun ψ => subdivChart cb.1 cb.2 s ψ)))).card : ℝ)
            ≤ ((∑ cb ∈ Φ₁, ∑ s ∈ (Finset.univ : Finset (Fin (n + 1) →
                Fin (3 * (subdivN n r - 1) + 1))), ((Ψ cb s).card)) : ℕ) := by
          refine Nat.cast_le.mpr ?_
          exact le_trans Finset.card_biUnion_le
            (Finset.sum_le_sum (fun cb _ => le_trans Finset.card_biUnion_le
              (Finset.sum_le_sum (fun s _ => Finset.card_image_le))))
        have h2 : (((∑ cb ∈ Φ₁, ∑ s ∈ (Finset.univ : Finset (Fin (n + 1) →
                Fin (3 * (subdivN n r - 1) + 1))), ((Ψ cb s).card)) : ℕ) : ℝ)
            = ∑ cb ∈ Φ₁, ∑ s : Fin (n + 1) → Fin (3 * (subdivN n r - 1) + 1),
                ((Ψ cb s).card : ℝ) := by
          push_cast
          rfl
        have h3 : (∑ cb ∈ Φ₁, ∑ s : Fin (n + 1) → Fin (3 * (subdivN n r - 1) + 1),
                ((Ψ cb s).card : ℝ))
            ≤ ∑ cb ∈ Φ₁, ((3 * (subdivN n r - 1) + 1) ^ (n + 1) : ℕ) * c₂ev := by
          refine Finset.sum_le_sum (fun cb hcb => ?_)
          calc ∑ s : Fin (n + 1) → Fin (3 * (subdivN n r - 1) + 1), ((Ψ cb s).card : ℝ)
              ≤ ∑ _s : Fin (n + 1) → Fin (3 * (subdivN n r - 1) + 1), c₂ev :=
                Finset.sum_le_sum (fun s _ => (hΨspec cb hcb s).1)
            _ = ((3 * (subdivN n r - 1) + 1) ^ (n + 1) : ℕ) * c₂ev := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
                  Fintype.card_fin, nsmul_eq_mul]
        have h4 : (∑ cb ∈ Φ₁, ((3 * (subdivN n r - 1) + 1) ^ (n + 1) : ℕ) * c₂ev)
            = (Φ₁.card : ℝ) * (((3 * (subdivN n r - 1) + 1) ^ (n + 1) : ℕ) * c₂ev) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        have h5 : (Φ₁.card : ℝ) * (((3 * (subdivN n r - 1) + 1) ^ (n + 1) : ℕ) * c₂ev)
            ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c
              * (((3 * K₀ + 4) ^ (n + 1) : ℕ) * ((r : ℝ) + 1) ^ (n + 1) * c₂ev) := by
          have hKrow : (((3 * (subdivN n r - 1) + 1) ^ (n + 1) : ℕ) : ℝ)
              ≤ ((3 * K₀ + 4) ^ (n + 1) : ℕ) * ((r : ℝ) + 1) ^ (n + 1) := by
            have hN' : (3 * (subdivN n r - 1) + 1) ^ (n + 1)
                ≤ (3 * K₀ + 4) ^ (n + 1) * (r + 1) ^ (n + 1) := by
              rw [← Nat.mul_pow]
              exact hKsub
            have hcast : (((3 * K₀ + 4) ^ (n + 1) * (r + 1) ^ (n + 1) : ℕ) : ℝ)
                = ((3 * K₀ + 4) ^ (n + 1) : ℕ) * ((r : ℝ) + 1) ^ (n + 1) := by
              push_cast
              ring
            calc (((3 * (subdivN n r - 1) + 1) ^ (n + 1) : ℕ) : ℝ)
                ≤ (((3 * K₀ + 4) ^ (n + 1) * (r + 1) ^ (n + 1) : ℕ) : ℝ) := by
                  exact_mod_cast hN'
              _ = ((3 * K₀ + 4) ^ (n + 1) : ℕ) * ((r : ℝ) + 1) ^ (n + 1) := hcast
          have hstep1 : (Φ₁.card : ℝ) * (((3 * (subdivN n r - 1) + 1) ^ (n + 1) : ℕ) * c₂ev)
              ≤ (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c)
                * (((3 * (subdivN n r - 1) + 1) ^ (n + 1) : ℕ) * c₂ev) :=
            mul_le_mul_of_nonneg_right hΦ₁card (mul_nonneg (Nat.cast_nonneg _) hc₂evnn)
          have hstep2 : (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c)
                * (((3 * (subdivN n r - 1) + 1) ^ (n + 1) : ℕ) * c₂ev)
              ≤ (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c)
                * (((3 * K₀ + 4) ^ (n + 1) : ℕ) * ((r : ℝ) + 1) ^ (n + 1) * c₂ev) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hKrow hc₂evnn) hc₁nn
          exact le_trans hstep1 hstep2
        have h6 : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c
              * (((3 * K₀ + 4) ^ (n + 1) : ℕ) * ((r : ℝ) + 1) ^ (n + 1) * c₂ev)
            = MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cB := by
          rw [hcB, MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_mul,
            MvPolynomial.eval_C, MvPolynomial.eval_pow, MvPolynomial.eval_add,
            MvPolynomial.eval_X, MvPolynomial.eval_C]
          rw [show MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c₂' = c₂ev by
            rw [hc₂evdef, hc₂' D r k (-Real.log ε)]
            have hb1 : MvPolynomial.eval ![D, r] (MvPolynomial.X 0 + 2 * b₁)
                = D + 2 * MvPolynomial.eval ![D, r] b₁ := by simp
            have hb : ((MvPolynomial.eval ![D, r] (MvPolynomial.X 0 + 2 * b₁) : ℕ) : ℝ)
                + ((Kpull + 2 : ℕ) : ℝ) = (Dg : ℝ) := by
              rw [hb1, hDg]
              push_cast
              ring
            have hl : -Real.log ε + Real.log 2 = -Real.log (ε / 2) := by
              rw [Real.log_div hε.ne' (by norm_num : (2 : ℝ) ≠ 0)]
              ring
            have hv : (![(((MvPolynomial.eval ![D, r] (MvPolynomial.X 0 + 2 * b₁) : ℕ) : ℝ)
                  + ((Kpull + 2 : ℕ) : ℝ)), (r : ℝ), (k : ℝ), -Real.log ε + Real.log 2]
                : Fin 4 → ℝ) = ![(Dg : ℝ), (r : ℝ), (k : ℝ), -Real.log (ε / 2)] := by
              funext i
              fin_cases i
              · show ((MvPolynomial.eval ![D, r] (MvPolynomial.X 0 + 2 * b₁) : ℕ) : ℝ)
                    + ((Kpull + 2 : ℕ) : ℝ) = (Dg : ℝ)
                exact hb
              · rfl
              · rfl
              · show -Real.log ε + Real.log 2 = -Real.log (ε / 2)
                exact hl
            rw [hv]]
          rw [show (![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] : Fin 4 → ℝ) 1 = (r : ℝ) from rfl]
          ring
        exact le_trans h1 (le_trans (by rw [h2]) (le_trans h3 (le_trans (by rw [h4])
          (le_trans h5 (by rw [h6])))))
      refine ⟨Φ₁.biUnion (fun cb => Finset.univ.biUnion (fun s =>
        (Ψ cb s).image (fun ψ => subdivChart cb.1 cb.2 s ψ))), ?_, ?_, ?_⟩
      · -- ## the cardinality bound
        refine le_trans hcard ?_
        rw [hcev]
        nlinarith [sq_nonneg (MvPolynomial.eval
          ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cB - 1 / 2)]
      · -- ## the per-chart conditions
        refine ChartsOK_biUnion (C := Φ₁) (f := fun cb => Finset.univ.biUnion (fun s =>
          (Ψ cb s).image (fun ψ => subdivChart cb.1 cb.2 s ψ))) ?_
        intro cb hcb
        refine ChartsOK_biUnion (C := (Finset.univ : Finset (Fin (n + 1) →
          Fin (3 * (subdivN n r - 1) + 1)))) (f := fun s =>
            (Ψ cb s).image (fun ψ => subdivChart cb.1 cb.2 s ψ)) ?_
        intro s _
        have hsub : ChartsOK S (a₁ + a₂ + A) (C * (MvPolynomial.eval ![D, r] b₁
            + MvPolynomial.eval ![Dg, r] b₂) + C) r Λ F
            ((Ψ cb s).image (fun ψ => subdivChart cb.1 cb.2 s ψ)) := by
          intro φ hφ
          obtain ⟨ψ, hψ, rfl⟩ := Finset.mem_image.mp hφ
          obtain ⟨hψgraph, hψrest⟩ := (hΨspec cb hcb s).2.1 ψ hψ
          refine ⟨fun j => ?_, fun l hl => ?_⟩
          · exact hSub (subdivN n r) s cb.1 cb.2 ψ a₁ a₂ (MvPolynomial.eval ![D, r] b₁)
              (MvPolynomial.eval ![Dg, r] b₂) (hΦ₁ok cb hcb).1 (hΦ₁ok cb hcb).2.1 hψgraph j
          · obtain ⟨hcube, hcont⟩ := hψrest l hl
            refine ⟨?_, ?_⟩
            · exact subdivChart_mem_openCubeW hNpos ((hΦ₁ok cb hcb).2.2) hcube
            · intro i
              refine ⟨?_, ?_⟩
              · refine (hcont i).1.congr (fun t _ => ?_)
                exact (fam_comp_subdivChart F cb.1 cb.2 s ψ i l t).symm
              · intro m hm t ht
                have hg := (hcont i).2 m hm t ht
                have hev : (fun u => F i l (fun j => subdivChart cb.1 cb.2 s ψ j l u))
                    =ᶠ[nhds t] (fun u => subdivFam F cb.1 cb.2 s i l (fun j => ψ j l u)) := by
                  refine Filter.eventually_of_mem ((openCube_isOpen (n + 1)).mem_nhds ht)
                    (fun u _ => ?_)
                  exact (fam_comp_subdivChart F cb.1 cb.2 s ψ i l u).symm
                rw [(hev.iteratedFDeriv ℝ m).eq_of_nhds]
                exact hg
        refine ChartsOK_mono_stage hsub (by omega) ?_
        show C * (MvPolynomial.eval ![D, r] b₁ + MvPolynomial.eval ![Dg, r] b₂) + C
          ≤ MvPolynomial.eval ![D, r] (bge + b₂)
        rw [MvPolynomial.eval_add, hbge, MvPolynomial.eval_add, MvPolynomial.eval_mul,
          MvPolynomial.eval_C, MvPolynomial.eval_add]
        have hb1 : MvPolynomial.eval ![D, r] (MvPolynomial.X 0 + 2 * b₁)
            = D + 2 * MvPolynomial.eval ![D, r] b₁ := by simp
        have hfun : (fun i : Fin 2 => MvPolynomial.eval ![D, r]
            (![(MvPolynomial.X 0 + 2 * b₁ + MvPolynomial.C (Kpull + 2)), MvPolynomial.X 1] i))
            = ![Dg, r] := by
          funext i
          fin_cases i
          · show MvPolynomial.eval ![D, r]
              (MvPolynomial.X 0 + 2 * b₁ + MvPolynomial.C (Kpull + 2)) = Dg
            rw [MvPolynomial.eval_add, hb1, MvPolynomial.eval_C, hDg]
            ring
          · simp
        rw [hb₂s, eval_eval₂_C_nat, hfun]
        exact Nat.le_add_right _ _
      · -- ## the `ε`-cover
        exact covers_subdivChartW hNpos hP.2 (fun cb hcb => (hΦ₁ok cb hcb).2.2) hΦ₁cov
          (fun cb hcb s => (hΨspec cb hcb s).2.2)

end Work.WilG4cW
