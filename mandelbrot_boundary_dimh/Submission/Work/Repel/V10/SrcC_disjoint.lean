import Mathlib
import Submission.Work.Repel.V10.chain_v9_src
import Submission.Work.L62.chain

namespace Work.Repel.V10

open MandelDim Complex Set Metric Filter Topology

/-- `fibImg j k` is the `φ₁`-image of the fibre `fib j k = W j + k`. -/
theorem fibImg_eq (V : Work.Repel.V10) (j : ℕ) (k : ℤ) :
    V.fibImg j k = V.P₁.φ '' V.fib j k := rfl

/-- **Distinct cells have disjoint fibre images.**  For `(j,k) ≠ (j',k')` the images
`φ₁ '' (W j + k)` and `φ₁ '' (W j' + k')` are disjoint, using `φ₁` injective on `Sm1 ⊇` both
fibres and the two structural facts about the chain: for `j ≠ j'` the `π`-images of `W j` and
`W j'` are disjoint (`IsChain.disjoint`) while `π` is `ℤ`-periodic; for `j = j'`, `k ≠ k'` the
centre distance `|k - k'| ≥ 1` exceeds `diam (W j) < 1/2` (`IsChain.bounded`). -/
theorem fibImg_disjoint (V : Work.Repel.V10) {j j' : ℕ} {k k' : ℤ}
    (hSm : V.fib j k ⊆ V.Sm1) (hSm' : V.fib j' k' ⊆ V.Sm1)
    (hne : (j, k) ≠ (j', k')) :
    Disjoint (V.fibImg j k) (V.fibImg j' k') := by
  rw [Set.disjoint_left]
  intro ζ hζ hζ'
  rw [fibImg_eq V, Set.mem_image] at hζ
  obtain ⟨u, hu, rfl⟩ := hζ
  rw [fibImg_eq V, Set.mem_image] at hζ'
  obtain ⟨v, hv, hvu⟩ := hζ'
  -- `φ₁ u = φ₁ v` with both points in `Sm1`: injectivity gives `u = v`.
  have hvu' : v = u := V.Sm1_injOn (hSm' hv) (hSm hu) hvu
  have hu' : u ∈ V.fib j' k' := hvu' ▸ hv
  -- write `u = a + k = b + k'` with `a ∈ W j`, `b ∈ W j'`.
  rw [fib, Set.mem_image] at hu hu'
  obtain ⟨a, ha, hau⟩ := hu
  obtain ⟨b, hb, hbu⟩ := hu'
  have h_eq : a + (k : ℂ) = b + (k' : ℂ) := hau.trans hbu.symm
  have hab : a = b + (((k' - k : ℤ)) : ℂ) := by
    push_cast
    linear_combination h_eq
  rcases eq_or_ne j j' with hjj | hjj
  · -- same level: `k ≠ k'`, and `|k - k'| ≥ 1 > diam (W j)`.
    have hkk : k ≠ k' := fun hh => hne (by rw [hjj, hh])
    have hnorm : (1 : ℝ) ≤ ‖a - b‖ := by
      have hsub : a - b = (((k' - k : ℤ)) : ℂ) := by rw [hab]; ring
      rw [hsub, Complex.norm_intCast]
      exact_mod_cast (Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hkk)))
    have hle : dist a b ≤ Metric.diam (V.W j) :=
      Metric.dist_le_diam_of_mem (V.hIsChain.bounded j).1 ha (hjj ▸ hb)
    rw [dist_eq_norm] at hle
    linarith [(V.hIsChain.bounded j).2]
  · -- different levels: `π a = π b`, contradicting `IsChain.disjoint`.
    have hπ : MandelDim.piExp a = MandelDim.piExp b := by
      rw [hab, Work.Horn.MandelDim.piExp_add_intCast]
    exact Set.disjoint_left.mp (V.hIsChain.disjoint j j' hjj)
      (mem_image_of_mem MandelDim.piExp ha)
      (hπ ▸ mem_image_of_mem MandelDim.piExp hb)

/-- **Distinct cells have disjoint source sets** `Raw j k = {w | s·π w ∈ φ₁ '' (W j + k)}`. -/
theorem Raw_disjoint (V : Work.Repel.V10) {j j' : ℕ} {k k' : ℤ}
    (hSm : V.fib j k ⊆ V.Sm1) (hSm' : V.fib j' k' ⊆ V.Sm1)
    (hne : (j, k) ≠ (j', k')) :
    Disjoint (V.Raw j k) (V.Raw j' k') := by
  rw [Set.disjoint_left]
  intro w hw hw'
  rw [Raw, Set.mem_ofPred_eq] at hw hw'
  exact Set.disjoint_left.mp (fibImg_disjoint V hSm hSm' hne) hw hw'

/-- **Distinct §6 cells have disjoint source regions.**  `V.SrcC j k n = V.Raw j k ∩
ball (V.wc j k + n) (1/2)`.  For distinct cells these are disjoint:

* distinct `(j,k)`: `Raw j k = {w | s·π w ∈ φ₁ '' (W j + k)}`.  If `j = j'` and `k ≠ k'` the
  fibres `W j + k`, `W j + k'` have centres `|k - k'| ≥ 1` apart while `diam (W j) < 1/2`
  (`IsChain.bounded`); if `j ≠ j'` then `IsChain.disjoint` gives `π '' W j ∩ π '' W j' = ∅` and
  `π` is `ℤ`-periodic (`Work.Horn.MandelDim.piExp_add_intCast`).  So the two fibres are disjoint,
  and `φ₁` is injective on `Sm1 ⊇` both (`hSm`, `hSm'`, `V.Sm1`, `φ_inj_up`/`φ_inj_dn`).
* equal `(j,k)`, distinct `n`: the round boxes `ball (V.wc j k + n) (1/2)` and
  `ball (V.wc j k + n') (1/2)` have centres `|n - n'| ≥ 1` apart, hence are disjoint.

This is needed to make the enclosing balls of the islands pairwise disjoint
(`Work.Repel.ReturnData.hdisj`). -/
theorem SrcC_disjoint (V : Work.Repel.V10) {j j' : ℕ} {k k' n n' : ℤ}
    (hSm : V.fib j k ⊆ V.Sm1) (hSm' : V.fib j' k' ⊆ V.Sm1)
    (hne : (j, k, n) ≠ (j', k', n')) :
    Disjoint (V.SrcC j k n) (V.SrcC j' k' n') := by
  rcases eq_or_ne (j, k) (j', k') with hjk | hjk
  · -- equal `(j,k)`: then `n ≠ n'`, and the two round boxes are disjoint.
    have hjj : j = j' := congrArg Prod.fst hjk
    have hkk : k = k' := congrArg Prod.snd hjk
    have hnn : n ≠ n' := fun h => hne (by rw [hjj, hkk, h])
    rw [Set.disjoint_left]
    intro w hw hw'
    rw [SrcC, Set.mem_inter_iff, Metric.mem_ball, dist_comm] at hw
    rw [SrcC, Set.mem_inter_iff, Metric.mem_ball, dist_comm] at hw'
    have htri : dist (V.wc j k + (n : ℂ)) (V.wc j' k' + (n' : ℂ)) < 1 := by
      calc dist (V.wc j k + (n : ℂ)) (V.wc j' k' + (n' : ℂ))
          ≤ dist (V.wc j k + (n : ℂ)) w + dist w (V.wc j' k' + (n' : ℂ)) :=
            dist_triangle _ _ _
        _ < 1 / 2 + 1 / 2 := by
            linarith [hw.2, hw'.2, dist_comm w (V.wc j' k' + (n' : ℂ))]
        _ = 1 := by norm_num
    have hge : (1 : ℝ) ≤ dist (V.wc j k + (n : ℂ)) (V.wc j' k' + (n' : ℂ)) := by
      rw [hjj, hkk, dist_eq_norm]
      have hsub : V.wc j' k' + (n : ℂ) - (V.wc j' k' + (n' : ℂ)) =
          (((n - n' : ℤ)) : ℂ) := by
        push_cast; ring
      rw [hsub, Complex.norm_intCast]
      exact_mod_cast (Int.one_le_abs (sub_ne_zero.mpr hnn))
    linarith
  · -- distinct `(j,k)`: the whole raw source sets are disjoint.
    rw [Set.disjoint_left]
    intro w hw hw'
    rw [SrcC, Set.mem_inter_iff] at hw hw'
    exact Set.disjoint_left.mp (Raw_disjoint V hSm hSm' hjk) hw.1 hw'.1

end Work.Repel.V10
