import Submission.Work.FrontierArcs
import Submission.Work.FlatBounded
import Submission.Work.FlatComponents
import Submission.Commons.Topology.Order.open_preconnected_bounded_eq_Ioo

open OptimalMoebius Topology Filter
open scoped BigOperators Matrix Topology Metric

set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# S4: frontier arcs are bounded open segments with seam-line endpoints

(S4 of T1-i, complete): the frontier arcs of a flat component `C` are
bounded open straight segments whose closure endpoints lie on the seam
lines.

* `closure_stripInterior_seam` — a point of `closure stripInterior`
  outside `stripInterior` has coordinate `x0 ∈ {0,1}` (pure metric
  argument: `abs_coord0_le_norm` + `Metric.mem_closure_iff`).
* **`frontierComponent_closure_point_on_seam`** — for an arc
  `K(e) = connectedComponentIn (∂C ∩ stripInterior) e`, every point of
  `closure K(e)` BEYOND the component lies on the seam lines
  (`x0 = 0` or `x0 = 1`).  Proof: `K(e) ⊆ stripInterior`;
  `frontierComponent_closed_in_strip` ((S3)) says
  `closure K(e) ∩ stripInterior ⊆ K(e)`, so a closure point outside
  `K(e)` is outside `stripInterior` — yet in `closure stripInterior`,
  hence on a seam.
* **`frontierComponent_bounded_real_segment`** — (S4 completion) with
  `C = flatComponent f p`, `p ∈ interior (FlatSet f)`, each arc
  `K(e)` is bounded (`frontier_flatComponent_bounded`, FlatBounded:
  `f` affine on `C` with isometric linear part and the whole strip
  image bounded), so its parameter set `S = {s | e + s•u ∈ K(e)}` is an
  open preconnected nonempty BOUNDED subset of ℝ — hence
  `S = (α,β)` with REAL endpoints
  (`Commons.Topology.Order.open_preconnected_bounded_eq_Ioo`, fleet
  lemma): `K(e) = {e + s•u | α < s < β}` is a bounded straight open
  segment; together with
  `frontierComponent_closure_point_on_seam` its two closure endpoints
  lie one on each seam `x0 = 0`, `x0 = 1`.

Build: `lake build Submission.Work.S4Seams` rc=0, zero sorry.
-/

noncomputable section
namespace Submission.PaperBand

/-- A closure point of `stripInterior` that is not in `stripInterior` has
coordinate `x0 ∈ {0,1}`: the closure of the open strip `{0<x0<1}` is the
closed strip `{0≤x0≤1}`. -/
lemma closure_stripInterior_seam {z : ℝ²} (hzcl : z ∈ closure stripInterior)
    (hzS : z ∉ stripInterior) : z 0 = 0 ∨ z 0 = 1 := by
  have hz0ge : 0 ≤ z 0 := by
    by_contra hlt
    have hz0 : z 0 < 0 := lt_of_not_ge hlt
    let ε : ℝ := -z 0 / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    rcases Metric.mem_closure_iff.mp hzcl ε hε with ⟨w, hwS, hwd⟩
    have hw0 : 0 < w 0 := by
      rw [stripInterior] at hwS
      exact hwS.1
    have hd : ‖w - z‖ < ε := by
      have hwd' : dist w z < ε := by simpa [dist_comm] using hwd
      simpa [dist_eq_norm] using hwd'
    have hco : |(w - z) 0| ≤ ‖w - z‖ := abs_coord0_le_norm (w - z)
    have hb0 : (w - z) 0 < ε :=
      lt_of_le_of_lt (le_trans (le_abs_self ((w - z) 0)) hco) hd
    have hrel : (w - z) 0 = w 0 - z 0 := by simp
    have hw0lt : w 0 < 0 := by
      dsimp [ε] at hb0
      linarith
    exact (not_lt_of_ge (le_of_lt hw0)) hw0lt
  have hz0le : z 0 ≤ 1 := by
    by_contra hgt
    have hz0 : 1 < z 0 := lt_of_not_ge hgt
    let ε : ℝ := (z 0 - 1) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    rcases Metric.mem_closure_iff.mp hzcl ε hε with ⟨w, hwS, hwd⟩
    have hw1 : w 0 < 1 := by
      rw [stripInterior] at hwS
      exact hwS.2
    have hd : ‖w - z‖ < ε := by
      have hwd' : dist w z < ε := by simpa [dist_comm] using hwd
      simpa [dist_eq_norm] using hwd'
    have hco : |(w - z) 0| ≤ ‖w - z‖ := abs_coord0_le_norm (w - z)
    have hb0 : -(w - z) 0 < ε :=
      lt_of_le_of_lt (le_trans (neg_le_abs ((w - z) 0)) hco) hd
    have hrel : (w - z) 0 = w 0 - z 0 := by simp
    have hw0gt : 1 < w 0 := by
      dsimp [ε] at hb0
      linarith
    exact (not_lt_of_ge (le_of_lt hw1)) hw0gt
  -- 0 ≤ z0 ≤ 1 and z ∉ stripInterior = {0<x0<1}
  have hznot : ¬(0 < z 0 ∧ z 0 < 1) := by
    intro h01
    rw [stripInterior] at hzS
    exact hzS h01
  by_cases hz0 : z 0 = 0
  · exact Or.inl hz0
  · right
    by_contra hz1
    have hz0p : 0 < z 0 := lt_of_le_of_ne hz0ge (Ne.symm hz0)
    have hz1m : z 0 < 1 := lt_of_le_of_ne hz0le hz1
    exact hznot ⟨hz0p, hz1m⟩
theorem frontierComponent_closure_point_on_seam {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p e z : ℝ²}
    (heS : e ∈ stripInterior) (heF : e ∈ frontier (flatComponent f p))
    (hzcl : z ∈ closure (connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e))
    (hzK : z ∉ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e) :
    z 0 = 0 ∨ z 0 = 1 := by
  have hS3 : closure (connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e) ∩
      stripInterior ⊆ connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e :=
    frontierComponent_closed_in_strip (f := f) (p := p) (e := e) heS heF
  have hzNS : z ∉ stripInterior := by
    intro hzS
    exact hzK (hS3 ⟨hzcl, hzS⟩)
  have hKsub : connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e ⊆
      stripInterior := by
    intro x hx
    exact (connectedComponentIn_subset (frontier (flatComponent f p) ∩ stripInterior) e hx).2
  have hzclS : z ∈ closure stripInterior := by
    exact closure_mono hKsub hzcl
  exact closure_stripInterior_seam hzclS hzNS


/-- **S4 (completion): a bounded frontier arc is an open straight segment
with REAL endpoints.**  For a flat component `C = flatComponent f p` (`p`
flat-interior) and `e ∈ ∂C ∩ stripInterior`, the frontier component
`K(e) := connectedComponentIn (∂C ∩ stripInterior) e` is bounded
(`frontier_flatComponent_bounded`), so its parameter set `S = {s | e +
s•u ∈ K(e)}` is an open preconnected nonempty BOUNDED subset of ℝ —
hence an interval `(α, β)` with REAL endpoints
(`Commons.Topology.Order.open_preconnected_bounded_eq_Ioo`).  Thus
`K(e) = {e + s•u | α < s < β}` is a bounded straight open segment. -/
theorem frontierComponent_bounded_real_segment {a : ℝ} {f : ℝ² → ℝ³}
    (hf : IsMoebiusEmbedding a f) (ha : 0 < a) {p : ℝ²} (hp : p ∈ interior (FlatSet f))
    {e : ℝ²} (heS : e ∈ stripInterior) (heF : e ∈ frontier (flatComponent f p)) :
    ∃ u : ℝ², ‖u‖ = 1 ∧ ∃ α β : ℝ, α < β ∧
      connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e =
        {x : ℝ² | ∃ s : ℝ, α < s ∧ s < β ∧ x = e + s • u} := by
  rcases frontierComponent_on_line hf ha heS heF with ⟨u, hu₁, hline⟩
  let K : Set ℝ² := connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e
  let S : Set ℝ := {s : ℝ | e + s • u ∈ K}
  have hSopen : IsOpen S := by
    dsimp [S, K]
    exact frontierComponent_paramSet_open hf ha hu₁ hline
  have hSpre : IsPreconnected S := by
    dsimp [S, K]
    exact paramSet_preconnected_of_preconnected (e := e) (u := u) hu₁
      (K := connectedComponentIn (frontier (flatComponent f p) ∩ stripInterior) e)
      (isPreconnected_connectedComponentIn (x := e)
        (F := frontier (flatComponent f p) ∩ stripInterior))
      (by
        intro y hy
        exact (mem_lineSet_iff e u y).mpr (hline y hy))
  have hSne : S.Nonempty := by
    refine ⟨0, ?_⟩
    dsimp [S, K]
    rw [zero_smul, add_zero]
    exact mem_connectedComponentIn ⟨heF, heS⟩
  have hSbd : ∃ R₀ : ℝ, ∀ s ∈ S, |s| ≤ R₀ := by
    have hxC : p ∈ flatComponent f p := mem_flatComponent hp
    rcases frontier_flatComponent_bounded hf ha hxC with ⟨R, hR0, hR⟩
    refine ⟨R + ‖p - e‖, ?_⟩
    intro s hs
    have hxK : e + s • u ∈ K := hs
    have hxfr : e + s • u ∈ frontier (flatComponent f p) := by
      exact (connectedComponentIn_subset (frontier (flatComponent f p) ∩ stripInterior) e hxK).1
    have hb : ‖(e + s • u) - p‖ ≤ R := hR (e + s • u) hxfr
    have hs_norm : ‖s • u‖ ≤ R + ‖p - e‖ := by
      calc
        ‖s • u‖ = ‖(e + s • u) - e‖ := by abel
        _ = ‖((e + s • u) - p) + (p - e)‖ := by abel
        _ ≤ ‖(e + s • u) - p‖ + ‖p - e‖ := norm_add_le ((e + s • u) - p) (p - e)
        _ ≤ R + ‖p - e‖ := add_le_add hb le_rfl
    have hmod : ‖s • u‖ = |s| := by
      rw [norm_smul]
      rw [hu₁]
      simp
    rw [hmod] at hs_norm
    exact hs_norm
  rcases (Commons.Topology.Order.open_preconnected_bounded_eq_Ioo hSopen hSne hSpre hSbd) with
    ⟨α, β, hαβ, hSeq⟩
  refine ⟨u, hu₁, α, β, hαβ, ?_⟩
  ext x
  constructor
  · intro hxK
    have hu_ne : u ≠ 0 := by
      intro h0
      rw [h0] at hu₁
      norm_num at hu₁
    have hxL : x ∈ lineSet e u := (mem_lineSet_iff e u x).mpr (hline x hxK)
    have hφ : signedLineFunc e u x = 0 := (mem_lineSet_iff e u x).mp hxL
    have hdet : det2 (x - e) u = 0 := by
      have h := hφ
      rwa [signedLineFunc_eq_det2 e u x] at h
    rcases exists_smul_of_det2_eq_zero hu_ne hdet with ⟨s₀, hs₀⟩
    have hxeq : x = e + s₀ • u := by
      calc x = e + (x - e) := by abel
        _ = e + s₀ • u := by rw [hs₀]
    have hs₀S : s₀ ∈ S := by
      dsimp [S]
      rwa [hxeq] at hxK
    have hs₀I : s₀ ∈ Set.Ioo α β := by
      rw [← hSeq]
      exact hs₀S
    exact ⟨s₀, hs₀I.1, hs₀I.2, hxeq⟩
  · rintro ⟨s, has, hsb, hxeq⟩
    have hsI : s ∈ Set.Ioo α β := ⟨has, hsb⟩
    have hsS : s ∈ S := by
      rw [hSeq]
      exact hsI
    have hseg : e + s • u ∈ K := hsS
    rw [hxeq]
    exact hseg

end Submission.PaperBand
