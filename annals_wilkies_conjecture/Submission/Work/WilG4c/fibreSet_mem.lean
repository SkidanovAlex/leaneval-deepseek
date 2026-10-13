import Mathlib
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG4c.graphOf_member_mem

namespace Work.WilG4c

open WilkiesDesign

/-! ### The `l`-fibre of an `Ω`-set

An `Ω`-set `A ⊆ ℝ^{p+N}` is a set of the form `S.Ω F D (p+N)`; its `l`-fibre along the first
`p` coordinates is `{z : ℝ^N | Fin.append l z ∈ A}`.  The point of this file is that the fibre
is again an `Ω`-set, with a format and a degree that are **uniform in** `l`, `A`, `F` and `D`:
the degree of the fibre is `D + K` and its format `F + K` for a constant `K` depending only on
`p` and `N`.

Mathematically the fibre is a *section*: fix the first `p` coordinates of the ambient
`ℝ^{p+N}` to the point `l`, then keep only the trailing `N` coordinates.  Both operations are
already available in the development:

* fixing coordinates to a constant is the intersection of the `p` coordinate hyperplanes
  `{z | z (Fin.castAdd N i) = l i}`, each of which is cut out by the *linear* polynomial
  `X (Fin.castAdd N i) - C (l i)`, hence lies in `Ω (p+N) 1 (p+N)`
  (`coordEqSet_mem_deg1`).  The intersection therefore costs only `+1` in the format and the
  sum `+p` in the degree — uniformly in `l`, since the constant is absorbed in the degree-one
  polynomial;
* keeping the trailing `N` coordinates is `Work.WilG5.lastN`, whose `Ω`-membership
  `Work.WilG5.lastN_mem` is the reindexing theorem of the G5 development.

So `{z | Fin.append l z ∈ A} = lastN N (A ∩ ⋂ i, {z | z (Fin.castAdd N i) = l i})`, and the
two membership statements compose. -/

/-- The set of points of `ℝ^{p+N}` whose first `p` coordinates are `l`, as an `Ω`-set.
Only `+1` in the format and `+p` in the degree are needed, uniformly in `l`. -/
theorem firstBlockSet_mem (S : WilkiesDesign.SOMin) (p N : ℕ) (l : Fin p → ℝ) :
    (⋂ i : Fin p, {z : Fin (p + N) → ℝ | z (Fin.castAdd N i) = l i}) ∈
      S.Ω (p + N + 1) p (p + N) := by
  have h := S.inter (D := fun _ : Fin p => 1)
    (A := fun i : Fin p => {z : Fin (p + N) → ℝ | z (Fin.castAdd N i) = l i})
    (fun i => coordEqSet_mem_deg1 (S := S) (Fin.castAdd N i) (l i))
  simpa using h

/-- The section identity: fixing the first `p` coordinates of `A` to `l` and keeping the
trailing `N` of them is exactly the `l`-fibre of `A`. -/
theorem lastN_inter_firstBlockSet_eq (p N : ℕ) (A : Set (Fin (p + N) → ℝ)) (l : Fin p → ℝ) :
    Work.WilG5.lastN N (A ∩ ⋂ i : Fin p, {z : Fin (p + N) → ℝ | z (Fin.castAdd N i) = l i})
      = {z : Fin N → ℝ | Fin.append l z ∈ A} := by
  ext u
  constructor
  · rintro ⟨x, hxA, hxH⟩
    have hxl : x = l := by
      funext i
      have h := Set.mem_iInter.mp hxH i
      simp only [Set.mem_ofPred_eq] at h
      rwa [Fin.append_left] at h
    rw [hxl] at hxA
    exact hxA
  · intro hu
    refine ⟨l, hu, ?_⟩
    rw [Set.mem_iInter]
    intro i
    exact Fin.append_left l u i

/-- The `l`-fibre `{z : ℝ^N | Fin.append l z ∈ A}` of an `Ω`-set `A ⊆ ℝ^{p+N}` is `Ω`-bounded,
with a format and a degree that are uniform in the parameter `l`. -/
theorem fibreSet_mem (S : WilkiesDesign.SOMin) (p N : ℕ) :
    ∃ K : ℕ, ∀ (F D : ℕ) (A : Set (Fin (p + N) → ℝ)) (l : Fin p → ℝ),
      A ∈ S.Ω F D (p + N) →
      {z : Fin N → ℝ | Fin.append l z ∈ A} ∈ S.Ω (F + K) (D + K) N := by
  refine ⟨(p + N + 3) + (N + (N + (p + N))) + (4 * (N + (p + N) + (N + (p + N))) + 8)
    + 1 + (N + (p + N)) + (N + (p + N)) + p + (2 * (N + (p + N)) + 4), ?_⟩
  intro F D A l hA
  have hH := firstBlockSet_mem S p N l
  have hA' : A ∈ S.Ω (F + (p + N + 2)) D (p + N) :=
    Work.WilG5.mem_mono hA _ _ (by omega) (le_refl D)
  have hH' : (⋂ i : Fin p, {z : Fin (p + N) → ℝ | z (Fin.castAdd N i) = l i}) ∈
      S.Ω (F + (p + N + 2)) p (p + N) :=
    Work.WilG5.mem_mono hH _ _ (by omega) (le_refl p)
  have hB : A ∩ ⋂ i : Fin p, {z : Fin (p + N) → ℝ | z (Fin.castAdd N i) = l i} ∈
      S.Ω (F + (p + N + 2) + 1) (D + p) (p + N) := by
    have h := S.inter (D := fun i : Fin 2 => if i = 0 then D else p)
      (A := fun i : Fin 2 => if i = 0 then A
        else (⋂ i : Fin p, {z : Fin (p + N) → ℝ | z (Fin.castAdd N i) = l i}))
      (by intro i
          fin_cases i
          · simpa using hA'
          · simpa using hH')
    rw [show (∑ i : Fin 2, (if i = 0 then D else p)) = D + p from by
      simp [Fin.sum_univ_two]] at h
    have he : (⋂ i : Fin 2, (if i = 0 then A
        else (⋂ i : Fin p, {z : Fin (p + N) → ℝ | z (Fin.castAdd N i) = l i})))
        = A ∩ ⋂ i : Fin p, {z : Fin (p + N) → ℝ | z (Fin.castAdd N i) = l i} := by
      ext z; simp [Fin.forall_fin_two]
    rw [he] at h
    exact h
  have hlast := Work.WilG5.lastN_mem (S := S) (n := p) N (F + (p + N + 2) + 1) (D + p) hB
  rw [lastN_inter_firstBlockSet_eq p N A l] at hlast
  exact Work.WilG5.mem_mono hlast _
    _ (by omega) (by omega)

end Work.WilG4c
