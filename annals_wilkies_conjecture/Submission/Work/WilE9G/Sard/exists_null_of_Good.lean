import Mathlib
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE5.Strat.flatConormalTools
import Submission.Work.WilE9G.Sard.sardOnLevelSet
import Submission.Work.WilE9G.Sard.goodFDerivSurjective

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
open scoped Topology
namespace Work.WilE9G.Sard

open WilkiesDesign WilkiesDesign.E
open Work.WilE9G

/-! ## `projBase0` is a continuous linear map -/

/-- The base projection as a continuous linear map. -/
def projBase0L {q n : ℕ} (hn : n ≤ q) : (Fin (0 + q) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin n =>
    ContinuousLinearMap.proj (R := ℝ) (Fin.cast (Nat.zero_add q).symm (Fin.castLE hn i)))

theorem projBase0_eq_projBase0L {q n : ℕ} (hn : n ≤ q) :
    projBase0 hn = ⇑(projBase0L hn) := by
  funext v i; rfl

theorem projBase0L_apply {q n : ℕ} (hn : n ≤ q) (v : Fin (0 + q) → ℝ) :
    projBase0L hn v = projBase0 hn v := by
  funext i; rfl

theorem analyticAt_projBase0 {q n : ℕ} (hn : n ≤ q) (x : Fin (0 + q) → ℝ) :
    AnalyticAt ℝ (projBase0 hn) x := by
  rw [projBase0_eq_projBase0L hn]
  exact (projBase0L hn).analyticAt x

theorem fderiv_projBase0 {q n : ℕ} (hn : n ≤ q) (x : Fin (0 + q) → ℝ) :
    fderiv ℝ (projBase0 hn) x = projBase0L hn := by
  rw [projBase0_eq_projBase0L hn]
  exact ContinuousLinearMap.fderiv (projBase0L hn)

/-! ## The two formulations of base-submersivity agree -/

theorem not_isBaseSubmersiveAt_iff {q n : ℕ} (hn : n ≤ q) (S : Stratum 0 q)
    (z : Fin (0 + q) → ℝ) :
    (¬ ∀ w : Fin n → ℝ, ∃ v : Fin (0 + q) → ℝ,
        fderiv ℝ (fun z : Fin (0 + q) → ℝ => fun a : Fin S.j => eaEval S.X.c (S.h a) z) z v = 0 ∧
        fderiv ℝ (projBase0 hn) z v = w)
      ↔ ¬ Stratum.IsBaseSubmersiveAt S hn z := by
  have hfd : fderiv ℝ (fun z : Fin (0 + q) → ℝ => fun a : Fin S.j => eaEval S.X.c (S.h a) z) z
      = ContinuousLinearMap.pi (fun a : Fin S.j =>
          fderiv ℝ (fun w : Fin (0 + q) → ℝ => eaEval S.X.c (S.h a) w) z) := by
    rw [fderiv_pi (fun a =>
      (Work.WilE5.Strat.analyticAt_eaEval S.X.c (S.h a) z).differentiableAt)]
  have hbody :
      (∀ w : Fin n → ℝ, ∃ v : Fin (0 + q) → ℝ,
          (ContinuousLinearMap.pi (fun a : Fin S.j =>
            fderiv ℝ (fun w : Fin (0 + q) → ℝ => eaEval S.X.c (S.h a) w) z)) v = 0 ∧
          projBase0L hn v = w)
        ↔ (∀ w : Fin n → ℝ, ∃ v : Fin (0 + q) → ℝ,
            projBase0 hn v = w ∧
            ∀ a : Fin S.j, fderiv ℝ (fun w : Fin (0 + q) → ℝ => eaEval S.X.c (S.h a) w) z v = 0) := by
    apply forall_congr'; intro w
    apply exists_congr; intro v
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by rw [← projBase0L_apply hn v]; exact h2, fun a => ?_⟩
      have := congrFun h1 a
      rwa [ContinuousLinearMap.pi_apply] at this
    · rintro ⟨h1, h2⟩
      refine ⟨?_, by rw [projBase0L_apply hn v]; exact h1⟩
      funext a
      rw [ContinuousLinearMap.pi_apply]
      exact h2 a
  rw [hfd, fderiv_projBase0 hn z]
  simp only [Stratum.IsBaseSubmersiveAt]
  constructor
  · intro h hB; exact h (hbody.mpr hB)
  · intro h hA; exact h (hbody.mp hA)

/-! ## The main theorem -/

theorem exists_null_of_Good {q n : ℕ} (hn : n ≤ q) (S : WilkiesDesign.E.Stratum 0 q)
    (hS : S.Good) :
    ∃ N₁ : Set (Fin n → ℝ), MeasureTheory.volume N₁ = 0 ∧
      ∀ z ∈ S.X.set, ¬ Work.WilE9G.Stratum.IsBaseSubmersiveAt S hn z →
        Work.WilE9G.projBase0 hn z ∈ N₁ := by
  set h : (Fin (0 + q) → ℝ) → (Fin S.j → ℝ) := fun z a => eaEval S.X.c (S.h a) z with hdef
  have hana : ∀ x, AnalyticAt ℝ h x := fun x =>
    AnalyticAt.pi (fun a => Work.WilE5.Strat.analyticAt_eaEval S.X.c (S.h a) x)
  have hzero : ∀ z ∈ S.X.set, h z = 0 := by
    intro z hz; funext a; exact (hS z hz).1 a
  -- the local input at every point of the stratum
  have key : ∀ z : ↥S.X.set, ∃ (N : Set (Fin n → ℝ)) (U : Set (Fin (0 + q) → ℝ)),
      MeasureTheory.volume N = 0 ∧ U ∈ 𝓝 (z : Fin (0 + q) → ℝ) ∧
      ∀ y ∈ U, h y = h (z : Fin (0 + q) → ℝ) → ¬ Stratum.IsBaseSubmersiveAt S hn y →
        projBase0 hn y ∈ N := by
    intro z
    obtain ⟨N, U, hN, hU, hconcl⟩ :=
      sardOnLevelSet h (projBase0 hn) hana (fun x => analyticAt_projBase0 hn x) z.1
        (goodFDerivSurjective S hS z.2)
    exact ⟨N, U, hN, hU, fun y hyU hyh hybad => hconcl y hyU hyh (by
      rw [not_isBaseSubmersiveAt_iff hn S y]; exact hybad)⟩
  choose N U hN hU hconcl using key
  -- countable subcover of the stratum
  have hlind : IsLindelof (S.X.set) := by
    rw [isLindelof_iff_lindelofSpace]; infer_instance
  obtain ⟨t, htcount, htcover⟩ := hlind.elim_nhds_subcover'
    (fun (x : Fin (0 + q) → ℝ) (hx : x ∈ S.X.set) => U ⟨x, hx⟩)
    (fun (x : Fin (0 + q) → ℝ) (hx : x ∈ S.X.set) => hU ⟨x, hx⟩)
  refine ⟨⋃ x ∈ t, N x, ?_, ?_⟩
  · have heq : (⋃ x ∈ t, N x) = ⋃ x : (t : Set ↥S.X.set), N x.1 := by
      ext y; constructor
      · intro hy
        obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp hy
        exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hy⟩
      · intro hy
        obtain ⟨x, hy⟩ := Set.mem_iUnion.mp hy
        exact Set.mem_iUnion₂.mpr ⟨x.1, x.2, hy⟩
    rw [heq]
    haveI : Countable ↥t := htcount.to_subtype
    exact measure_iUnion_null (fun x : (t : Set ↥S.X.set) => hN x.1)
  · intro y hy hybad
    obtain ⟨x, hx, hxU⟩ := Set.mem_iUnion₂.mp (htcover hy)
    exact Set.mem_iUnion₂.mpr ⟨x, hx,
      hconcl x y hxU (by rw [hzero y hy, hzero x x.2]) hybad⟩

end Work.WilE9G.Sard
