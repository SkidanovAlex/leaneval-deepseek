import Mathlib.Data.EReal.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.IntermediateValue

set_option linter.unusedVariables false

open Set

namespace Commons.Topology.Order

theorem open_preconnected_eq_Ioo_ereal {s : Set ℝ} (hs : IsOpen s) (hsne : s.Nonempty)
    (hpre : IsPreconnected s) :
    ∃ a b : EReal, s = {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b} := by
  classical
  let A : Set EReal := (fun z : ℝ => (z : EReal)) '' s
  refine ⟨sInf A, sSup A, ?_⟩
  have hord : s.OrdConnected := isPreconnected_iff_ordConnected.mp hpre
  ext x
  constructor
  · intro hx
    change sInf A < (x : EReal) ∧ (x : EReal) < sSup A
    constructor
    · obtain ⟨l, hlx, hl⟩ :=
        exists_Ioc_subset_of_mem_nhds (a := x) (s := s) (hs.mem_nhds hx) ⟨x - 1, by linarith⟩
      let v : ℝ := (l + x) / 2
      have hlv : l < v := by dsimp [v]; linarith
      have hvx : v < x := by dsimp [v]; linarith
      have hvs : v ∈ s := hl ⟨hlv, le_of_lt hvx⟩
      have hvA : (v : EReal) ∈ A := ⟨v, hvs, rfl⟩
      exact lt_of_le_of_lt (sInf_le hvA) (EReal.coe_lt_coe (x := v) (y := x) hvx)
    · obtain ⟨u, hxu, hu⟩ :=
        exists_Ico_subset_of_mem_nhds (a := x) (s := s) (hs.mem_nhds hx) ⟨x + 1, by linarith⟩
      let w : ℝ := (x + u) / 2
      have hxw : x < w := by dsimp [w]; linarith
      have hwu : w < u := by dsimp [w]; linarith
      have hws : w ∈ s := hu ⟨le_of_lt hxw, hwu⟩
      have hwA : (w : EReal) ∈ A := ⟨w, hws, rfl⟩
      exact lt_of_lt_of_le (EReal.coe_lt_coe (x := x) (y := w) hxw) (le_sSup hwA)
  · intro hx
    change sInf A < (x : EReal) ∧ (x : EReal) < sSup A at hx
    rcases hx with ⟨hax, hxb⟩
    have hyl : ∃ y ∈ s, (y : EReal) < (x : EReal) := by
      by_contra hbot
      have hle : (x : EReal) ≤ sInf A := by
        apply le_sInf
        intro z hz
        rcases hz with ⟨y, hys, hzy⟩
        rw [← hzy]
        exact le_of_not_gt fun hylt => hbot ⟨y, hys, hylt⟩
      exact (not_lt_of_ge hle) hax
    have hwg : ∃ w ∈ s, (x : EReal) < (w : EReal) := by
      by_contra htop
      have hle' : sSup A ≤ (x : EReal) := by
        apply sSup_le
        intro z hz
        rcases hz with ⟨w, hws, hzw⟩
        rw [← hzw]
        exact le_of_not_gt fun hxlt => htop ⟨w, hws, hxlt⟩
      exact (not_lt_of_ge hle') hxb
    rcases hyl with ⟨y, hys, hyx⟩
    rcases hwg with ⟨w, hws, hxw⟩
    have hyxR : y < x := EReal.coe_lt_coe_iff.mp hyx
    have hxwR : x < w := EReal.coe_lt_coe_iff.mp hxw
    exact hord.out hys hws ⟨le_of_lt hyxR, le_of_lt hxwR⟩

end Commons.Topology.Order