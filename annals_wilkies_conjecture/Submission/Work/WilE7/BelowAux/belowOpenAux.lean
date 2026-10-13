/-
  WilE7 (`Submission.Work.WilE7.BelowAux.belowOpenAux`): the auxiliary analytic/topological
  facts underlying the coverage of the **open** below cell by the connected component of
  `belowSopen`.

  This is the strict-lower-bound analogue of the three facts used for the closed below cell
  (`preconn_under_graph`, `belowPhi_continuous`, `belowPhi_mem`):

  * `preconn_under_graph_open` : the region `{q | q.1 ∈ C ∧ -1 < q.2 < σ q.1}` beneath the graph
    of a continuous `σ > -1` over a preconnected `C` is preconnected;
  * `belowPhi_continuousOn`    : the parametrisation `belowPhi s j` is continuous on *any* set
    whose first projection lands in the domain `C` of the sheet `s j`;
  * `belowPhi_mem_open`        : the parametrisation of the *open* region `belowHlt` lands in
    `belowSopen`.
-/
import Mathlib
import Submission.Work.WilE7.BelowAux.BelowDefs
import Submission.Work.WilE7.BelowAux.belowPhi_mem
import Submission.Work.WilE7.BelowAux.belowOpenDefs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.BelowAux
open WilkiesDesign WilkiesDesign.E

/-! ## §1. Preconnectedness of the strict region under a graph -/

/-- The region `{(x,t) : x ∈ C, -1 < t < σ x}` beneath the graph of `σ` is preconnected,
whenever `C` is preconnected and `σ` is continuous on `C` with `σ > -1` on `C`.

It is the continuous image of the preconnected set `C × (0,1)` under the bijection
`(x,s) ↦ (x, -1 + s·(σ x + 1))`. -/
theorem preconn_under_graph_open {α : Type*} [TopologicalSpace α] {C : Set α}
    (hC : IsPreconnected C) {σ : α → ℝ} (hσ : ContinuousOn σ C)
    (hσ1 : ∀ x ∈ C, -1 < σ x) :
    IsPreconnected {q : α × ℝ | q.1 ∈ C ∧ -1 < q.2 ∧ q.2 < σ q.1} := by
  let S : Set (α × ℝ) := C ×ˢ Set.Ioo (0 : ℝ) 1
  let F : α × ℝ → α × ℝ := fun p => (p.1, -1 + p.2 * (σ p.1 + 1))
  have hS : IsPreconnected S := hC.prod isPreconnected_Ioo
  have hσcont : ContinuousOn (fun p : α × ℝ => σ p.1) S :=
    hσ.comp continuous_fst.continuousOn (fun _ hp => hp.1)
  have hF : ContinuousOn F S := by
    refine ContinuousOn.prodMk continuous_fst.continuousOn ?_
    refine continuousOn_const.add (continuous_snd.continuousOn.mul ?_)
    exact hσcont.add continuousOn_const
  have himg : IsPreconnected (F '' S) := hS.image F hF
  have heq : F '' S = {q : α × ℝ | q.1 ∈ C ∧ -1 < q.2 ∧ q.2 < σ q.1} := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
      obtain ⟨hp2a, hp2b⟩ := hp2
      have hs : -1 < σ p.1 := hσ1 p.1 hp1
      refine ⟨hp1, ?_, ?_⟩
      · nlinarith [hp2a, hs]
      · nlinarith [hp2a, hp2b, hs]
    · rintro ⟨hq1, hq2a, hq2b⟩
      have hs : -1 < σ q.1 := hσ1 q.1 hq1
      refine ⟨(q.1, (q.2 + 1) / (σ q.1 + 1)), ?_, ?_⟩
      · refine ⟨hq1, ?_, ?_⟩
        · exact div_pos (by linarith) (by linarith)
        · rw [div_lt_one (by linarith : (0 : ℝ) < σ q.1 + 1)]
          linarith
      · refine Prod.ext rfl ?_
        simp only [F]
        rw [div_mul_cancel₀ _ (by linarith : σ q.1 + 1 ≠ 0)]
        ring
  rw [← heq]
  exact himg

/-! ## §2. Continuity of the parametrisation on any admissible region -/

/-- The parametrisation `belowPhi s j q = belowPt q.1 (s j (π_p q.1)) q.2` is continuous on any
set whose first projection lands in the domain `C` of the (continuous on `C`) sheet `s j`. -/
theorem belowPhi_continuousOn {p m k : ℕ} (C : Set (Fin p → ℝ))
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k)
    (hcont : ContinuousOn (s j) C) (D : Set ((Fin (p + (m + 1)) → ℝ) × ℝ))
    (hD : ∀ q ∈ D, projFirst p (m + 1) q.1 ∈ C) :
    ContinuousOn (belowPhi s j) D := by
  have hfst : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ => q.1) D :=
    continuous_fst.continuousOn
  have hpi : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      projFirst p (m + 1) q.1) D :=
    (Work.WilE7.continuous_projFirst p (m + 1)).comp_continuousOn hfst
  have hsj : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      s j (projFirst p (m + 1) q.1)) D :=
    hcont.comp hpi hD
  have hA : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append (projFirst p (m + 1) q.1) (s j (projFirst p (m + 1) q.1))) D :=
    (Fin.continuous_append (X := ℝ) p (m + 1)).comp_continuousOn (hpi.prodMk hsj)
  have hp1 : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append q.1 (Fin.append (projFirst p (m + 1) q.1)
        (s j (projFirst p (m + 1) q.1)))) D :=
    (Fin.continuous_append (X := ℝ) (p + (m + 1)) (p + (m + 1))).comp_continuousOn
      (hfst.prodMk hA)
  have hconst : ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      (fun _ : Fin 1 => q.2)) D :=
    (continuous_pi (fun _ => continuous_snd)).continuousOn
  have hfin := (Fin.continuous_append (X := ℝ) (belowK p m) 1).comp_continuousOn
      (hp1.prodMk hconst)
  show ContinuousOn (fun q : (Fin (p + (m + 1)) → ℝ) × ℝ =>
      Fin.append (Fin.append q.1 (Fin.append (projFirst p (m + 1) q.1)
        (s j (projFirst p (m + 1) q.1)))) (fun _ : Fin 1 => q.2)) D
  exact hfin

/-! ## §3. The parametrisation of the strict region lands in `belowSopen` -/

/-- The parametrisation `belowPhi s j` maps the *open* region `belowHlt` into `belowSopen`. -/
theorem belowPhi_mem_open {p m k : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ)) (j : Fin k)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set) :
    ∀ q ∈ belowHlt Z s j u₀, belowPhi s j q ∈ (belowSopen Z S).set := by
  intro q hq
  rw [mem_belowHlt] at hq
  obtain ⟨hq1, hqlo, hqhi⟩ := hq
  rw [belowSopen_mem_iff]
  refine ⟨belowPhi_mem S Z u₀ C hC s j hsub q ?_, ?_⟩
  · rw [mem_belowH]
    exact ⟨hq1, le_of_lt hqlo, hqhi⟩
  · rw [belowT_belowPhi]
    exact hqlo

end Work.WilE7.BelowAux
