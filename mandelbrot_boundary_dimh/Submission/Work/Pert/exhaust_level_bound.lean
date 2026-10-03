import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Basic
import Submission.Work.Parab.Setup

namespace Work.Pert

open Set

/-! ## Elementary consequences of the `ParabData` axioms

`Dφ` is closed under the backward translation `w ↦ w - 1` (`left_inv`), so *every* backward
translate of a point of `Dφ` is again in `Dφ`; and the Abel equation `φ (w+1) = f₀ (φ w)`
therefore iterates along the whole backward walk. -/

/-- Every backward translate of a point of `Dφ` lies in `Dφ`. -/
lemma sub_nat_mem_Dφ {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {w : ℂ}
    (hw : w ∈ d.Dφ) : ∀ j : ℕ, w - (j : ℂ) ∈ d.Dφ := by
  intro j
  induction j with
  | zero => simpa using hw
  | succ k ih =>
      have h := d.left_inv (w - (k : ℂ)) ih
      have heq : w - ((k + 1 : ℕ) : ℂ) = w - (k : ℂ) - 1 := by
        push_cast
        ring
      rwa [heq]

/-- The iterated Abel equation in backward form: `φ w = f₀^[n] (φ (w - n))`. -/
lemma φ_iterate_sub {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (n : ℕ) {w : ℂ}
    (hw : w ∈ d.Dφ) : d.φ w = f₀^[n] (d.φ (w - (n : ℂ))) := by
  induction n generalizing w with
  | zero => simp
  | succ k ih =>
      have hw1 : w - 1 ∈ d.Dφ := d.left_inv w hw
      have habel : d.φ w = f₀ (d.φ (w - 1)) := by
        have h := d.φ_abel (w - 1) hw1 (by simpa using hw)
        simpa using h
      rw [habel, ih hw1]
      have hcast : w - 1 - (k : ℂ) = w - ((k + 1 : ℕ) : ℂ) := by
        push_cast
        ring
      rw [hcast, Function.iterate_succ_apply']

/-- **Uniform bound on the level on a compact set.**  On a compact `K' ⊆ Dφ` the "exhaustion
level" of `d.exhaust` is bounded: there is `N` such that every `w ∈ K'` has a translate
`w - m`, `m ≤ N`, inside the sector `QLeft ξ₀`. -/
lemma exists_level_le_of_compact {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} (hK'c : IsCompact K') (hK' : K' ⊆ d.Dφ) :
    ∃ N : ℕ, ∀ w ∈ K', ∃ m : ℕ, m ≤ N ∧ w - (m : ℂ) ∈ MandelDim.QLeft d.ξ₀ := by
  -- The family of closed sets of points having no translate up to level `N` inside `QLeft ξ₀`.
  let W : ℕ → Set ℂ := fun N => {w : ℂ | ∀ m : ℕ, m ≤ N → w - (m : ℂ) ∉ MandelDim.QLeft d.ξ₀}
  have hclosed : ∀ N : ℕ, IsClosed (W N) := by
    intro N
    have hset : W N
        = ⋂ m : ℕ, ⋂ (_ : m ≤ N), {w : ℂ | w - (m : ℂ) ∉ MandelDim.QLeft d.ξ₀} := by
      ext w
      simp [W, Set.mem_iInter]
    rw [hset]
    refine isClosed_iInter fun m => isClosed_iInter fun _ => ?_
    exact ((Work.Parab.isOpen_QLeft d.ξ₀).isClosed_compl).preimage
      (continuous_id.sub continuous_const)
  -- `W` is decreasing in `N`, hence directed for `⊇`.
  have hmono : ∀ {i j : ℕ}, i ≤ j → W j ⊆ W i := by
    intro i j hij w hw m hm
    exact hw m (le_trans hm hij)
  -- No point of `K'` survives in every `W N` (that would contradict `exhaust`).
  have hdisj : Disjoint K' (⋂ N, W N) := by
    rw [Set.disjoint_left]
    intro w hwK hwAll
    obtain ⟨m, hm⟩ := d.exhaust w (hK' hwK)
    exact (Set.mem_iInter.mp hwAll m) m le_rfl hm
  obtain ⟨N, hN⟩ := hK'c.elim_directed_family_closed W hclosed hdisj
    (fun i j => ⟨max i j, hmono (le_max_left i j), hmono (le_max_right i j)⟩)
  refine ⟨N, fun w hwK => ?_⟩
  by_contra hcon
  exact (Set.disjoint_left.mp hN hwK) (fun m hm hmem => hcon ⟨m, hm, hmem⟩)

/-- **The `d.exhaust` level is uniformly bounded on a compact subset of the maximal domain.**
For `d : ParabData f₀ D₀` and `K'` compact with `K' ⊆ d.Dφ` there is `N` such that every `w ∈ K'`
has a *level* `n ≤ N` with `w - n ∈ QLeft d.ξ₀` (hence `w - j ∈ d.Dφ` for all `j ≤ n`, by
`left_inv`) and `d.φ w = f₀^[n] (d.φ (w - n))` (the iterated Abel equation).

Proof route (compactness): the sets `U_N := Dφ ∩ ⋃_{m ≤ N} (QLeft ξ₀ + m)` are open and increasing
with `⋃_N U_N = Dφ` (⊆ by `exhaust`; ⊇ because if `w - m ∈ QLeft ξ₀ ⊆ Dφ` then
`w - m + 1 ∈ Dφ` by `succ_iff` + `Q_maps`), so `K' ⊆ U_N` for some `N`.  Take the minimal such
`n` (`Nat.find`); the walk conjunct is `left_inv` iterated, and the Abel conjunct follows by
induction on `n` from `φ_abel`.  (Alternatively, the minimal level of `d.exhaust` satisfies
`w - n ∈ QLeft ξ₀`, `w - n + 1 ∉ QLeft ξ₀`, which forces `Re (w - n) ≥ -1 - ξ₀`, hence
`n ≤ Re w + 1 + ξ₀`, and `Re` is bounded above on the compact `K'`.) -/
theorem exhaust_level_bound {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} (hK'c : IsCompact K') (hK' : K' ⊆ d.Dφ) :
    ∃ N : ℕ, ∀ w ∈ K', ∃ n : ℕ, n ≤ N ∧ w - (n : ℂ) ∈ MandelDim.QLeft d.ξ₀ ∧
      (∀ j : ℕ, j ≤ n → w - (j : ℂ) ∈ d.Dφ) ∧ d.φ w = f₀^[n] (d.φ (w - (n : ℂ))) := by
  obtain ⟨N, hN⟩ := exists_level_le_of_compact d hK'c hK'
  refine ⟨N, fun w hw => ?_⟩
  obtain ⟨n, hnN, hnQ⟩ := hN w hw
  exact ⟨n, hnN, hnQ, fun j _ => sub_nat_mem_Dφ d (hK' hw) j,
    φ_iterate_sub d n (hK' hw)⟩

end Work.Pert
