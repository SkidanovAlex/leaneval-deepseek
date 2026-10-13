import Mathlib
import Submission.Work.WilG4c.Defs

namespace Work.WilG4c

/-- The affine slice `x' ↦ pt x' y` is a continuous map `ℝ → ℝ^{n+1}`. -/
lemma continuous_pt {n : ℕ} (y : Fin n → ℝ) : Continuous (fun x' : ℝ => Work.WilkG4c.pt x' y) := by
  rw [continuous_pi_iff]
  intro i
  induction i using Fin.cases with
  | zero => exact continuous_id
  | succ j => exact continuous_const

/-- A nonempty open subset of `ℝ` is infinite. -/
lemma infinite_of_isOpen_nonempty {o : Set ℝ} (ho : IsOpen o) (hne : o.Nonempty) :
    o.Infinite := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨ε, hε, hεo⟩ := (Metric.isOpen_iff.mp ho) a ha
  refine (Set.Ioo_infinite (show a - ε < a + ε by linarith)).mono ?_
  intro y hy
  exact hεo (by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)

/-- The "good" `x`-coordinates — inside `I`, outside the finite bad set `B`, and with `pt x y`
in a given open set `U` — accumulate at every point `x ∈ I` whose own `pt x y` lies in `U`. -/
lemma mem_closure_good_pts {n : ℕ} (B : Finset ℝ) {y : Fin n → ℝ} {U : Set (Fin (n + 1) → ℝ)}
    (hU : IsOpen U) {x : ℝ} (hxU : Work.WilkG4c.pt x y ∈ U) (hxI : x ∈ Work.WilkG4c.I) :
    x ∈ closure {x' : ℝ | x' ∈ Work.WilkG4c.I ∧ x' ∉ (B : Set ℝ) ∧
      Work.WilkG4c.pt x' y ∈ U} := by
  -- Membership in the closure is tested against open neighbourhoods of `x`.
  rw [mem_closure_iff]
  intro o ho hxo
  -- The interval `I` is open.
  have hIopen : IsOpen (Work.WilkG4c.I) := by
    unfold Work.WilkG4c.I
    exact isOpen_Ioo
  -- The set of "candidate" points is open around `x`.
  have hTopen : IsOpen (Work.WilkG4c.I ∩ {x' : ℝ | Work.WilkG4c.pt x' y ∈ U}) :=
    hIopen.inter (hU.preimage (continuous_pt y))
  have hxT : x ∈ Work.WilkG4c.I ∩ {x' : ℝ | Work.WilkG4c.pt x' y ∈ U} := ⟨hxI, hxU⟩
  -- `o` intersected with these candidates is a nonempty open set in `ℝ`, hence infinite,
  -- so it cannot be contained in the finite set `B`.
  have hopen : IsOpen (o ∩ (Work.WilkG4c.I ∩ {x' : ℝ | Work.WilkG4c.pt x' y ∈ U})) :=
    ho.inter hTopen
  obtain ⟨x', hx's, hx'B⟩ :=
    (infinite_of_isOpen_nonempty hopen ⟨x, hxo, hxT⟩).exists_notMem_finite B.finite_toSet
  exact ⟨x', hx's.1, hx's.2.1, hx'B, hx's.2.2⟩

end Work.WilG4c
