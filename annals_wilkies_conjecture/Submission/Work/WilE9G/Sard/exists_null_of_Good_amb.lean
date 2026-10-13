import Mathlib
import Submission.Work.WilE9G.Amb
import Submission.Work.WilE9G.Sard.exists_null_of_Good
import Submission.Work.WilE9G.Sard.goodFDerivSurjective_amb
import Submission.Work.WilE9G.Sard.isBaseSubmersiveAt_iff_pi_amb

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
open scoped Topology
namespace Work.WilE9G.Sard

open WilkiesDesign WilkiesDesign.E
open Work.WilE9G

/-! ## The base projection as a continuous linear map

`projBase hn : ℝ^N → ℝ^n` is the projection onto the first `n` coordinates.  It is the
underlying map of the continuous linear map `projBaseL hn`, whence it is analytic with
derivative `projBaseL hn` everywhere. -/

/-- The base projection as a continuous linear map. -/
def projBaseL {N n : ℕ} (hn : n ≤ N) : (Fin N → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin n => ContinuousLinearMap.proj (Fin.castLE hn i))

theorem projBase_eq_projBaseL {N n : ℕ} (hn : n ≤ N) :
    projBase hn = ⇑(projBaseL hn) := by
  funext v i; rfl

theorem projBaseL_apply {N n : ℕ} (hn : n ≤ N) (v : Fin N → ℝ) :
    projBaseL hn v = projBase hn v := by
  funext i; rfl

theorem analyticAt_projBase {N n : ℕ} (hn : n ≤ N) (x : Fin N → ℝ) :
    AnalyticAt ℝ (projBase hn) x := by
  rw [projBase_eq_projBaseL hn]
  exact (projBaseL hn).analyticAt x

theorem fderiv_projBase {N n : ℕ} (hn : n ≤ N) (x : Fin N → ℝ) :
    fderiv ℝ (projBase hn) x = projBaseL hn := by
  rw [projBase_eq_projBaseL hn]
  exact ContinuousLinearMap.fderiv (projBaseL hn)

/-! ## The theorem -/

/-- **Sard for an ambient `Good` stratum**: the set of points of `S.X.set` at which the base
projection `π_n` is not submersive has null image in `ℝ^n`.

The proof is global: at every point `z₀` of the stratum the equations of `S` are a surjective
analytic map `h : ℝ^N → ℝ^{S.j}` (`goodFDerivSurjective_amb`), so `sardOnLevelSet` gives a
parametrisation of the fibre `{h = h z₀}` near `z₀` and a null set which absorbs the critical
values of the base projection restricted to that fibre.  A countable (Lindelöf) subcover of the
stratum then combines the local pieces. -/
theorem exists_null_of_Good_amb {N n : ℕ} (hn : n ≤ N) (S : Work.WilE9G.AmbStratum N)
    (hS : S.Good) :
    ∃ N₁ : Set (Fin n → ℝ), MeasureTheory.volume N₁ = 0 ∧
      ∀ z ∈ S.X.set, ¬ Work.WilE9G.AmbStratum.IsBaseSubmersiveAt S hn z →
        Work.WilE9G.projBase hn z ∈ N₁ := by
  set h : (Fin N → ℝ) → (Fin S.j → ℝ) := fun z a => eaEval S.X.c (S.h a) z with hdef
  have hana : ∀ x, AnalyticAt ℝ h x := fun x =>
    AnalyticAt.pi (fun a => Work.WilE5.Strat.analyticAt_eaEval S.X.c (S.h a) x)
  have hzero : ∀ z ∈ S.X.set, h z = 0 := by
    intro z hz; funext a; exact (hS z hz).1 a
  -- the local input at every point of the stratum
  have key : ∀ z : ↥S.X.set, ∃ (N₁ : Set (Fin n → ℝ)) (U : Set (Fin N → ℝ)),
      MeasureTheory.volume N₁ = 0 ∧ U ∈ 𝓝 (z : Fin N → ℝ) ∧
      ∀ y ∈ U, h y = h (z : Fin N → ℝ) → ¬ AmbStratum.IsBaseSubmersiveAt S hn y →
        projBase hn y ∈ N₁ := by
    intro z
    obtain ⟨N₁, U, hN, hU, hconcl⟩ :=
      sardOnLevelSet h (projBase hn) hana (fun x => analyticAt_projBase hn x) z.1
        (goodFDerivSurjective_amb S hS z.2)
    exact ⟨N₁, U, hN, hU, fun y hyU hyh hybad => hconcl y hyU hyh (by
      intro hcontra
      apply hybad
      rw [isBaseSubmersiveAt_iff_pi_amb hn S y]
      intro w
      obtain ⟨v, hv0, hvw⟩ := hcontra w
      exact ⟨v, by rw [← projBaseL_apply hn v, ← fderiv_projBase hn y]; exact hvw,
             by rw [← hdef]; exact hv0⟩)⟩
  choose N₁ U hN hU hconcl using key
  -- countable subcover of the stratum
  have hlind : IsLindelof (S.X.set) := by
    rw [isLindelof_iff_lindelofSpace]; infer_instance
  obtain ⟨t, htcount, htcover⟩ := hlind.elim_nhds_subcover'
    (fun (x : Fin N → ℝ) (hx : x ∈ S.X.set) => U ⟨x, hx⟩)
    (fun (x : Fin N → ℝ) (hx : x ∈ S.X.set) => hU ⟨x, hx⟩)
  refine ⟨⋃ x ∈ t, N₁ x, ?_, ?_⟩
  · have heq : (⋃ x ∈ t, N₁ x) = ⋃ x : (t : Set ↥S.X.set), N₁ x.1 := by
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
