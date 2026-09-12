import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.unusedSectionVars false

open scoped Real

namespace Commons.Geometry.Convex.Hadwiger

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]

/-- Reassociation of an affine combination. -/
lemma affine_comb_eq (a : ℝ) (x y : V) : (1 - a) • x + a • y = x + a • (y - x) := by
  calc
    (1 - a) • x + a • y = (1 - a) • x + a • (x + (y - x)) := by
      rw [show x + (y - x) = y by abel]
    _ = (1 - a) • x + (a • x + a • (y - x)) := by rw [smul_add]
    _ = ((1 - a) + a) • x + a • (y - x) := by rw [← add_assoc, ← add_smul]
    _ = x + a • (y - x) := by rw [show (1 - a) + a = 1 by ring, one_smul]

/-- Core "first exit along a path" lemma.  If `f : ℝ → V` is continuous, starts inside the
closed set `P`, and the set of `t ≥ 0` with `f t ∈ P` is bounded above by `L`, then at the
supremum `t₀` of that set the point `f t₀` belongs to `P` but not to its interior. -/
lemma exists_frontier_of_sSup (P : Set V) (hPcl : IsClosed P) {f : ℝ → V}
    (hf : Continuous f) (hf0 : f 0 ∈ P) (L : ℝ)
    (hL : ∀ ⦃t : ℝ⦄, 0 ≤ t → f t ∈ P → t ≤ L) :
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ ≤ L ∧
      t₀ = sSup {t : ℝ | 0 ≤ t ∧ f t ∈ P} ∧ f t₀ ∈ P ∧ f t₀ ∉ interior P := by
  set S : Set ℝ := {t : ℝ | 0 ≤ t ∧ f t ∈ P} with hSdef
  have hS0 : (0 : ℝ) ∈ S := by
    dsimp [S]
    exact ⟨le_rfl, hf0⟩
  have hSne : S.Nonempty := ⟨(0 : ℝ), hS0⟩
  have hScl : IsClosed S := by
    have hEq : S = {t : ℝ | f t ∈ P} ∩ Set.Ici (0 : ℝ) := by
      ext t
      constructor
      · intro ht
        exact ⟨ht.2, ht.1⟩
      · intro ht
        exact ⟨ht.2, ht.1⟩
    rw [hEq]
    exact (IsClosed.preimage hf hPcl).inter isClosed_Ici
  have hSsub : S ⊆ Set.Icc (0 : ℝ) L := by
    intro t ht
    exact ⟨ht.1, hL ht.1 ht.2⟩
  have hScomp : IsCompact S :=
    IsCompact.of_isClosed_subset isCompact_Icc hScl hSsub
  have hbdd : BddAbove S := ⟨L, fun t ht => (hSsub ht).2⟩
  let t₀ : ℝ := sSup S
  have ht₀mem : t₀ ∈ S := by
    dsimp [t₀]
    exact IsCompact.sSup_mem hScomp hSne
  have ht₀ge0 : 0 ≤ t₀ := ht₀mem.1
  have ht₀leL : t₀ ≤ L := hL ht₀ge0 ht₀mem.2
  have hft₀P : f t₀ ∈ P := ht₀mem.2
  have hgt : ∀ ⦃t : ℝ⦄, t₀ < t → f t ∉ P := by
    intro t ht hft
    have ht0 : 0 ≤ t := le_trans ht₀ge0 ht.le
    have htS : t ∈ S := ⟨ht0, hft⟩
    have hle : t ≤ sSup S := le_csSup hbdd htS
    have : ¬ t₀ < t := not_lt_of_ge (by simpa [t₀] using hle)
    exact this ht
  have hnotInt : f t₀ ∉ interior P := by
    intro hy
    rcases mem_interior.mp hy with ⟨U, hUP, hUopen, hyU⟩
    rcases Metric.isOpen_iff.mp hUopen (f t₀) hyU with ⟨ε, hε0, hball⟩
    rcases Metric.continuousAt_iff.mp hf.continuousAt ε hε0 with ⟨δ, hδ0, hδ⟩
    let t : ℝ := t₀ + δ / 2
    have ht₀lt : t₀ < t := by
      dsimp [t]
      linarith
    have htdist : dist t t₀ < δ := by
      rw [dist_eq_norm]
      rw [Real.norm_eq_abs]
      have hsub : t - t₀ = δ / 2 := by
        dsimp [t]
        ring
      rw [hsub]
      rw [abs_of_pos (div_pos hδ0 (by norm_num : (0 : ℝ) < 2))]
      linarith
    have hftball : f t ∈ Metric.ball (f t₀) ε := by
      rw [Metric.mem_ball]
      exact hδ htdist
    have hftU : f t ∈ U := hball hftball
    have hftP : f t ∈ P := hUP hftU
    have htS : t ∈ S := ⟨le_trans ht₀ge0 ht₀lt.le, hftP⟩
    have hle : t ≤ sSup S := le_csSup hbdd htS
    have : ¬ t₀ < t := not_lt_of_ge (by simpa [t₀] using hle)
    exact this ht₀lt
  refine ⟨t₀, ht₀ge0, ht₀leL, ?_, hft₀P, hnotInt⟩
  rfl

/-- If `O` lies in the interior of the closed convex set `P` and `w ∉ P`, then the segment
`[O, w]` meets the frontier of `P`. -/
lemma exists_frontier_mem_segment_of_mem_interior_not_mem (P : Set V)
    (hPcvx : Convex ℝ P) (hPcpt : IsCompact P) {O w : V} (hO : O ∈ interior P)
    (hw : w ∉ P) : ∃ y : V, y ∈ frontier P ∧ y ∈ segment ℝ O w := by
  have hPcl : IsClosed P := hPcpt.isClosed
  have hOP : O ∈ P := interior_subset hO
  let d : V := w - O
  let f : ℝ → V := fun t : ℝ => O + t • d
  have hf : Continuous f := by
    have hsmul : Continuous (fun t : ℝ => t • d) :=
      Continuous.smul continuous_id continuous_const
    simpa [f] using hsmul.const_add O
  have hf0 : f 0 ∈ P := by
    simpa [f, d] using hOP
  have hsc : StarConvex ℝ O P := hPcvx hOP
  have hL : ∀ ⦃t : ℝ⦄, 0 ≤ t → f t ∈ P → t ≤ 1 := by
    intro t ht0 hft
    by_contra hle
    have ht1 : 1 < t := lt_of_not_ge hle
    have htpos : 0 < t := lt_trans zero_lt_one ht1
    have htne : t ≠ 0 := ne_of_gt htpos
    have ha0 : 0 ≤ 1 - 1 / t := by
      have hd1 : (1 : ℝ) / t ≤ 1 := (div_le_iff₀ htpos).2 (by linarith)
      exact sub_nonneg.mpr hd1
    have hb0 : 0 ≤ 1 / t := le_of_lt (div_pos zero_lt_one htpos)
    have hab : (1 - 1 / t) + 1 / t = 1 := by ring
    have hmemP : (1 - 1 / t) • O + (1 / t) • f t ∈ P := hsc hft ha0 hb0 hab
    have hcalc : (1 - 1 / t) • O + (1 / t) • f t = w := by
      calc
        (1 - 1 / t) • O + (1 / t) • f t
            = (1 - 1 / t) • O + (1 / t) • (O + t • (w - O)) := by
                rw [show f t = O + t • (w - O) by simp [f, d]]
        _ = (1 - 1 / t) • O + ((1 / t) • O + (1 / t) • (t • (w - O))) := by
                rw [smul_add]
        _ = ((1 - 1 / t) + 1 / t) • O + ((1 / t) * t) • (w - O) := by
                rw [← add_assoc, ← add_smul, ← smul_smul]
        _ = O + (w - O) := by
                rw [show (1 - 1 / t) + 1 / t = 1 by ring, div_mul_cancel₀ (1 : ℝ) htne]
                simp
        _ = w := by
                abel
    have hwP : w ∈ P := by
      rwa [hcalc] at hmemP
    exact hw hwP
  rcases exists_frontier_of_sSup P hPcl hf hf0 1 hL with ⟨t₀, ht₀ge0, ht₀le1, ht₀eq, hft₀P, hnotInt⟩
  refine ⟨f t₀, ?_, ?_⟩
  · rw [IsClosed.frontier_eq hPcl]
    exact ⟨hft₀P, hnotInt⟩
  · rw [segment_eq_image]
    refine ⟨t₀, ⟨ht₀ge0, ht₀le1⟩, ?_⟩
    calc
      (1 - t₀) • O + t₀ • w = O + t₀ • (w - O) := by rw [affine_comb_eq]
      _ = f t₀ := by
        simp [f, d]

/-- If `O` is in the interior of the compact convex set `P` and `x ∈ P`, `x ≠ O`, then moving
from `O` through `x` one first meets the frontier of `P` at a point `y` beyond `x`, and
`x ∈ [O, y]`. -/
lemma exists_frontier_on_segment_of_mem_interior_ne (P : Set V) (_hPcvx : Convex ℝ P)
    (hPcpt : IsCompact P) {O x : V} (hO : O ∈ interior P) (hx : x ∈ P) (hxO : x ≠ O) :
    ∃ y : V, y ∈ frontier P ∧ x ∈ segment ℝ O y := by
  have hPcl : IsClosed P := hPcpt.isClosed
  have hOP : O ∈ P := interior_subset hO
  let d : V := x - O
  let f : ℝ → V := fun t : ℝ => O + t • d
  have hf : Continuous f := by
    have hsmul : Continuous (fun t : ℝ => t • d) :=
      Continuous.smul continuous_id continuous_const
    simpa [f] using hsmul.const_add O
  have hf0 : f 0 ∈ P := by
    simpa [f, d] using hOP
  have hd0 : d ≠ 0 := by
    intro hd
    exact hxO (sub_eq_zero.mp (by simpa [d] using hd))
  have hnormd : 0 < ‖d‖ := norm_pos_iff.mpr hd0
  obtain ⟨R, hPsub⟩ := hPcpt.isBounded.subset_closedBall O
  have hL : ∀ ⦃t : ℝ⦄, 0 ≤ t → f t ∈ P → t ≤ R / ‖d‖ := by
    intro t ht0 hft
    have hftball : f t ∈ Metric.closedBall O R := hPsub hft
    have hdist : dist (f t) O ≤ R := Metric.mem_closedBall.mp hftball
    have hnorm : ‖f t - O‖ ≤ R := by
      rwa [dist_eq_norm] at hdist
    have hnorm2 : t * ‖d‖ ≤ R := by
      have h1 : ‖f t - O‖ = t * ‖d‖ := by
        calc
          ‖f t - O‖ = ‖t • d‖ := by rw [show f t - O = t • d by simp [f]]
          _ = t * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      linarith
    exact (le_div_iff₀ hnormd).2 hnorm2
  rcases exists_frontier_of_sSup P hPcl hf hf0 (R / ‖d‖) hL with
    ⟨t₀, ht₀ge0, ht₀leL, ht₀eq, hft₀P, hnotInt⟩
  -- t₀ ≥ 1 because 1 ∈ S
  have h1S : 1 ≤ t₀ := by
    have h1mem : (1 : ℝ) ∈ {t : ℝ | 0 ≤ t ∧ f t ∈ P} := by
      refine ⟨by norm_num, ?_⟩
      simpa [f, d] using hx
    have hbdd : BddAbove {t : ℝ | 0 ≤ t ∧ f t ∈ P} :=
      ⟨R / ‖d‖, fun t ht => hL ht.1 ht.2⟩
    have hle : (1 : ℝ) ≤ sSup {t : ℝ | 0 ≤ t ∧ f t ∈ P} := le_csSup hbdd h1mem
    simpa [ht₀eq] using hle
  have ht₀pos : 0 < t₀ := lt_of_lt_of_le zero_lt_one h1S
  refine ⟨f t₀, ?_, ?_⟩
  · rw [IsClosed.frontier_eq hPcl]
    exact ⟨hft₀P, hnotInt⟩
  · rw [segment_eq_image]
    refine ⟨1 / t₀, ?_, ?_⟩
    · constructor
      · exact div_nonneg zero_le_one (le_of_lt ht₀pos)
      · have hd1 : (1 : ℝ) / t₀ ≤ 1 := (div_le_iff₀ ht₀pos).2 (by linarith)
        exact hd1
    · calc
        (1 - 1 / t₀) • O + (1 / t₀) • f t₀ = O + (1 / t₀) • (f t₀ - O) := by
            rw [affine_comb_eq]
        _ = O + (1 / t₀) • (t₀ • d) := by
            rw [show f t₀ - O = t₀ • d by simp [f]]
        _ = O + (1 / t₀ * t₀) • d := by rw [smul_smul]
        _ = O + d := by
            rw [div_mul_cancel₀ (1 : ℝ) (ne_of_gt ht₀pos)]
            simp
        _ = x := by
            simp [d]

theorem exists_frontier_on_segment_of_mem_interior {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
    (hV : 0 < Module.finrank ℝ V)
    {P : Set V} (hPcvx : Convex ℝ P) (hPcpt : IsCompact P) {O x : V}
    (hO : O ∈ interior P) (hx : x ∈ P) :
    ∃ y : V, y ∈ frontier P ∧ x ∈ segment ℝ O y := by
  classical
  by_cases hxO : x = O
  · subst x
    have hNt : Nontrivial V := Module.finrank_pos_iff.mp hV
    obtain ⟨v, hv0⟩ : ∃ v : V, v ≠ 0 := by
      rcases hNt.exists_pair_ne with ⟨a, b, hab⟩
      by_cases ha : a = 0
      · refine ⟨b, ?_⟩
        intro hb0
        exact hab (by simp [ha, hb0])
      · exact ⟨a, ha⟩
    have hnormv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    obtain ⟨R, hPsub⟩ := hPcpt.isBounded.subset_closedBall O
    have hR0 : 0 ≤ R := by
      have hOcl : dist O O ≤ R := Metric.mem_closedBall.mp (hPsub (interior_subset hO))
      simpa using hOcl
    let c : ℝ := (R + 1) / ‖v‖
    have hc0 : 0 ≤ c := by
      dsimp [c]
      exact div_nonneg (by linarith) (le_of_lt hnormv)
    let w : V := O + c • v
    have hw : w ∉ P := by
      intro hwP
      have hwball : dist w O ≤ R := Metric.mem_closedBall.mp (hPsub hwP)
      have hdistw : dist w O = R + 1 := by
        rw [dist_eq_norm]
        calc
          ‖w - O‖ = ‖c • v‖ := by rw [show w - O = c • v by simp [w]]
          _ = c * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
          _ = R + 1 := by
            dsimp [c]
            exact div_mul_cancel₀ (R + 1) (ne_of_gt hnormv)
      have hle : R + 1 ≤ R := by
        rwa [hdistw] at hwball
      linarith
    rcases exists_frontier_mem_segment_of_mem_interior_not_mem (P := P) hPcvx hPcpt hO hw with
      ⟨y, hyf, hyseg⟩
    refine ⟨y, hyf, ?_⟩
    exact left_mem_segment ℝ O y
  · exact exists_frontier_on_segment_of_mem_interior_ne P hPcvx hPcpt hO hx hxO

end Commons.Geometry.Convex.Hadwiger