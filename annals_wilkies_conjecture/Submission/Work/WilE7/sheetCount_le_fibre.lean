import Mathlib
import Submission.Work.Wilkies.E.Spec

namespace Work.WilE7

open WilkiesDesign.E

/-- Two tuples in `ℝ^{p+q}` are recovered from their first `p` and last `q` coordinates. -/
theorem append_projFirst_projSnd {p q : ℕ} (z : Fin (p + q) → ℝ) :
    Fin.append (projFirst p q z) (projSnd p q z) = z := by
  funext i
  refine Fin.addCases (fun l => ?_) (fun r => ?_) i
  · simp [projFirst]
  · simp [projSnd]

/-- An upper bound on the number of pairwise disjoint "sheets" that all meet every fibre over
`C`: since `x₀ ∈ C`, each sheet contributes a distinct point of the fibre over `x₀`. -/
theorem sheetCount_le_fibre
    {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (C : Set (Fin p → ℝ)) (x₀ : Fin p → ℝ)
    (hx₀ : x₀ ∈ C)
    (hfin : (WilkiesDesign.E.fiber S.X.set x₀).Finite)
    (Ds : Finset (Set (Fin (p + q) → ℝ)))
    (hsub : ∀ Z ∈ Ds, Z ⊆ S.X.set)
    (hdisj : ∀ Z ∈ Ds, ∀ Z' ∈ Ds, Z ≠ Z' → Disjoint Z Z')
    (hmeet : ∀ Z ∈ Ds, ∀ c ∈ C, ∃ z ∈ Z, WilkiesDesign.E.projFirst p q z = c) :
    Ds.card ≤ (WilkiesDesign.E.fiber S.X.set x₀).ncard := by
  classical
  -- every `Z ∈ Ds` meets the fibre of `S.X.set` over `x₀`
  have key : ∀ Z ∈ Ds, ∃ z, z ∈ Z ∧ projFirst p q z = x₀ := fun Z hZ => hmeet Z hZ x₀ hx₀
  -- choose one point of each sheet, lying over `x₀`
  let w : {Z // Z ∈ Ds} → (Fin (p + q) → ℝ) := fun Z => Classical.choose (key Z.1 Z.2)
  have hw_mem : ∀ Z : {Z // Z ∈ Ds}, w Z ∈ Z.1 :=
    fun Z => (Classical.choose_spec (key Z.1 Z.2)).1
  have hw_proj : ∀ Z : {Z // Z ∈ Ds}, projFirst p q (w Z) = x₀ :=
    fun Z => (Classical.choose_spec (key Z.1 Z.2)).2
  -- record the last `q` coordinates of the chosen point: these lie in the fibre over `x₀`
  let g : {Z // Z ∈ Ds} → (Fin q → ℝ) := fun Z => projSnd p q (w Z)
  have hg_mem : Set.MapsTo g ↑Ds.attach ↑hfin.toFinset := by
    intro Z _
    change g Z ∈ hfin.toFinset
    rw [hfin.mem_toFinset]
    have h1 : Fin.append x₀ (g Z) = w Z := by rw [← hw_proj Z, append_projFirst_projSnd]
    show Fin.append x₀ (g Z) ∈ S.X.set
    rw [h1]
    exact hsub Z.1 Z.2 (hw_mem Z)
  have hg_inj : Set.InjOn g ↑Ds.attach := by
    intro Z _ Z' _ heq
    by_contra hne
    -- equality of the last `q` coordinates forces equality of the chosen points
    have hw_eq : w Z = w Z' := by
      have h1 : Fin.append x₀ (g Z) = w Z := by rw [← hw_proj Z, append_projFirst_projSnd]
      have h2 : Fin.append x₀ (g Z') = w Z' := by rw [← hw_proj Z', append_projFirst_projSnd]
      rw [← h1, ← h2, heq]
    -- ... which is a common point of two disjoint sheets
    have hd : Disjoint Z.1 Z'.1 := hdisj Z.1 Z.2 Z'.1 Z'.2 (fun h => hne (Subtype.ext h))
    exact (Set.disjoint_left.mp hd) (hw_mem Z) (hw_eq ▸ hw_mem Z')
  have hcard := Finset.card_le_card_of_injOn g hg_mem hg_inj
  rw [Finset.card_attach] at hcard
  have h2 : hfin.toFinset.card = (WilkiesDesign.E.fiber S.X.set x₀).ncard :=
    (Set.ncard_eq_toFinset_card _ hfin).symm
  omega

end Work.WilE7
