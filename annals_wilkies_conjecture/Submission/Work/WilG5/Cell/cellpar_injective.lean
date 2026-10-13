import Mathlib
import Submission.Work.WilG5.Defs

namespace Work.WilG5.Cell

/-- The free-coordinate map of a `CellPar` parametrisation is injective.

If `e i = e j` for `i ≠ j`, then the "local surjectivity" clause (clause 6) applied at a point
`y ∈ κ` — whose free coordinates `y ∘ e` lie in the open cube by clause 5 — would, for every
parameter `v` in the open cube close enough to `y ∘ e`, have to produce a point `z` of `κ`
whose value at both `e i` and `e j` equals the *two different* prescribed values `v i` and
`v j`.  That is impossible since `z (e i) = z (e j)`.  Choosing such a `v` (necessarily exists
because the open cube is an open neighbourhood of `y ∘ e`) gives the contradiction. -/
theorem cellpar_injective {n d : ℕ} {κ : Set (Fin n → ℝ)} {e : Fin d → Fin n}
    {R : Set (Fin (d + n) → ℝ)} (hpar : Work.WilG5.CellPar n κ d e R) (hne : κ.Nonempty) :
    Function.Injective e := by
  intro i j hij
  by_contra hneij
  obtain ⟨y, hy⟩ := hne
  -- clause 5: the free coordinates of `y` lie in the open cube
  have hcube : ∀ k : Fin d, y (e k) ∈ Set.Ioo (0 : ℝ) 1 := hpar.2.2.2.2.1 y hy
  -- clause 6 (local surjectivity) at `y`, with a fixed tolerance `η = 1`
  obtain ⟨ε, hεpos, hε⟩ := hpar.2.2.2.2.2 y hy 1 (by norm_num)
  have hcp : 0 < y (e i) := (Set.mem_Ioo.mp (hcube i)).1
  have hclt : y (e i) < 1 := (Set.mem_Ioo.mp (hcube i)).2
  -- a shift making the `i`-th free coordinate differ from `y (e i)` while staying in `(0,1)`
  set δ : ℝ := min (ε / 2) ((1 - y (e i)) / 2) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (by linarith) (by linarith)
  set t : ℝ := y (e i) + δ with ht
  have ht_ne : t ≠ y (e i) := by
    intro h; rw [ht] at h; linarith
  have ht_mem : t ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [Set.mem_Ioo]
    constructor
    · rw [ht]; linarith
    · rw [ht]
      have h2 : δ ≤ (1 - y (e i)) / 2 := by rw [hδ]; exact min_le_right _ _
      linarith
  have htdist : |t - y (e i)| < ε := by
    have h1 : δ ≤ ε / 2 := by rw [hδ]; exact min_le_left _ _
    have hnn : 0 ≤ t - y (e i) := by rw [ht]; linarith
    rw [abs_of_nonneg hnn]; linarith
  -- the nearby parameter `v`, differing from `y ∘ e` only in the `i`-th coordinate
  set v : Fin d → ℝ := Function.update (fun k => y (e k)) i t with hv
  have hv_cube : v ∈ WilkiesDesign.openCube d := by
    intro k
    rcases eq_or_ne k i with hk | hk
    · rw [hk, hv, Function.update_self]; exact ht_mem
    · rw [hv, Function.update_of_ne hk]; exact hcube k
  have hv_close : ∀ k, |v k - y (e k)| < ε := by
    intro k
    rcases eq_or_ne k i with hk | hk
    · rw [hk, hv, Function.update_self]; exact htdist
    · rw [hv, Function.update_of_ne hk]; simpa using hεpos
  obtain ⟨z, _hzR, _hzη, hze⟩ := hε v hv_cube hv_close
  -- `z (e i) = v i = t` but `z (e j) = v j = y (e j)`, and `e i = e j`
  have h1 : z (e i) = t := by
    have hh := hze i
    rw [hv, Function.update_self] at hh
    exact hh
  have h2 : z (e j) = y (e j) := by
    have := hze j
    rw [hv, Function.update_of_ne (Ne.symm hneij)] at this
    exact this
  rw [hij] at h1
  have ht_eq : t = y (e i) := by
    rw [← h1, h2, hij]
  exact ht_ne ht_eq

end Work.WilG5.Cell
