import Mathlib
import Submission.Work.WilE9G.Sard.exists_null_of_Good
import Submission.Work.WilE9G.Sard.sardOnLevelSet
import Submission.Work.WilE9G.Sard.goodFDerivSurjective

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
open scoped Topology

namespace Work.WilE7.DimAPI

open WilkiesDesign WilkiesDesign.E

theorem locus_null_of_good_analytic {q r : ℕ} (S : WilkiesDesign.E.Stratum 0 q) (hS : S.Good)
    (F : (Fin (0 + q) → ℝ) → (Fin r → ℝ)) (hF : ∀ x, AnalyticAt ℝ F x) :
    ∃ N₁ : Set (Fin r → ℝ), MeasureTheory.volume N₁ = 0 ∧
      ∀ z ∈ S.X.set,
        (¬ ∀ w : Fin r → ℝ, ∃ v : Fin (0 + q) → ℝ,
            fderiv ℝ (fun z' : Fin (0 + q) → ℝ => fun a : Fin S.j =>
              WilkiesDesign.E.eaEval S.X.c (S.h a) z') z v = 0 ∧
            fderiv ℝ F z v = w) → F z ∈ N₁ := by
  set h : (Fin (0 + q) → ℝ) → (Fin S.j → ℝ) := fun z a => eaEval S.X.c (S.h a) z with hdef
  have hana : ∀ x, AnalyticAt ℝ h x := fun x =>
    AnalyticAt.pi (fun a => Work.WilE5.Strat.analyticAt_eaEval S.X.c (S.h a) x)
  have hzero : ∀ z ∈ S.X.set, h z = 0 := by
    intro z hz; funext a; exact (hS z hz).1 a
  -- At each point of the stratum there is a neighbourhood and a null set capturing the
  -- critical values of `F` on the level set `h = 0`.
  have key : ∀ z : ↥S.X.set, ∃ (N : Set (Fin r → ℝ)) (U : Set (Fin (0 + q) → ℝ)),
      MeasureTheory.volume N = 0 ∧ U ∈ 𝓝 (z : Fin (0 + q) → ℝ) ∧
      ∀ y ∈ U, h y = h (z : Fin (0 + q) → ℝ) →
        (¬ ∀ w : Fin r → ℝ, ∃ v : Fin (0 + q) → ℝ,
            fderiv ℝ (fun z' : Fin (0 + q) → ℝ => fun a : Fin S.j =>
              eaEval S.X.c (S.h a) z') y v = 0 ∧
            fderiv ℝ F y v = w) → F y ∈ N := by
    intro z
    exact Work.WilE9G.Sard.sardOnLevelSet h F hana hF z.1
      (Work.WilE9G.Sard.goodFDerivSurjective S hS z.2)
  choose N U hN hU hconcl using key
  -- Countable subcover of the stratum.
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
      hconcl x y hxU (by rw [hzero y hy, hzero x.1 x.2]) hybad⟩

end Work.WilE7.DimAPI
