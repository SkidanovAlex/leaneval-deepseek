import Mathlib
import Submission.Work.ShafarevichKoch.ProTwoClosed

/-!
# `Work.ShafarevichKoch.hasProTwoPresentationClosed_mono`

The closed (pro-`2`) form of the Shafarevich--Koch relation bound,
`HasProTwoPresentationClosed F d r` (`ProTwoClosed.lean`), is recorded with `r` *relators*.  The
statement proved here is that the bound is **monotone in the number of relators**: a presentation
with `r` relators is *a fortiori* a presentation with `r' ≥ r` relators, obtained by padding the
relator family with the empty word.

The only point needing care is that `HasProTwoPresentationClosed` carries, besides the closed
kernel condition (`ClosedRelationData`), the clause that the abstract group

`presentedGroup d r w = FreeGroup (Fin d) ⧸ Subgroup.normalClosure (Set.range w)`

is residually a finite `2`-group.  Padding with `1` does not change the normal closure of the
relator set, hence does not change the presented group, so the residual-`2`-finiteness clause is
transported across the relabelling of the quotient (`QuotientGroup.quotientMulEquivOfEq` +
`residuallyFiniteTwoGroup_of_mulEquiv`).

## Main results

* `pad_normalClosure` -- padding the relator family with `1` does not change its normal closure;
* `pad_closedRelationData` -- the closed relation condition survives padding;
* `residuallyFiniteTwoGroup_presented_congr` -- residual `2`-finiteness of the presented group
  depends only on the normal closure of the relators;
* `hasProTwoPresentationClosed_mono` -- the target.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **Padding the relator family with `1` does not change its normal closure.**  If `r ≤ r'`, the
family `Fin r' → FreeGroup (Fin d)` obtained from `w : Fin r → FreeGroup (Fin d)` by sending
`i ≥ r` to the empty word has the same normal closure as `w`. -/
theorem pad_normalClosure {d r r' : ℕ} (hr : r ≤ r') (w : Fin r → FreeGroup (Fin d)) :
    Subgroup.normalClosure (Set.range (fun i : Fin r' =>
      if hi : (i : ℕ) < r then w ⟨(i : ℕ), hi⟩ else 1)) =
    Subgroup.normalClosure (Set.range w) := by
  apply le_antisymm
  · refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨i, rfl⟩
    show (if hi : (i : ℕ) < r then w ⟨(i : ℕ), hi⟩ else 1) ∈
      Subgroup.normalClosure (Set.range w)
    by_cases hi : (i : ℕ) < r
    · rw [dite_eq_left hi]
      exact Subgroup.subset_normalClosure ⟨⟨(i : ℕ), hi⟩, rfl⟩
    · rw [dite_eq_right hi]
      exact Subgroup.one_mem _
  · refine Subgroup.normalClosure_le_normal ?_
    rintro x ⟨j, rfl⟩
    have hj : (j : ℕ) < r' := lt_of_lt_of_le j.isLt hr
    have heq : (fun i : Fin r' => if hi : (i : ℕ) < r then w ⟨(i : ℕ), hi⟩ else 1)
        ⟨(j : ℕ), hj⟩ = w j := by
      show (if hi : ((⟨(j : ℕ), hj⟩ : Fin r') : ℕ) < r then
        w ⟨((⟨(j : ℕ), hj⟩ : Fin r') : ℕ), hi⟩ else 1) = w j
      rw [dite_eq_left j.isLt]
    rw [← heq]
    exact Subgroup.subset_normalClosure ⟨⟨(j : ℕ), hj⟩, rfl⟩

/-- **The closed relation condition survives padding.**  Any `r` words satisfying
`ClosedRelationData` may be padded with `1` (for `r ≤ r'`) to `r'` words satisfying
`ClosedRelationData`: the extra relator is trivial, so it holds among the `g_i` and no finite
`2`-quotient of the free group is lost. -/
theorem pad_closedRelationData {G : Type*} [Group G] {d r r' : ℕ} {g : Fin d → G}
    {w : Fin r → FreeGroup (Fin d)} (h : ClosedRelationData d r g w) (hr : r ≤ r') :
    ClosedRelationData d r' g (fun i : Fin r' =>
      if hi : (i : ℕ) < r then w ⟨(i : ℕ), hi⟩ else 1) := by
  constructor
  · intro i
    show (if hi : (i : ℕ) < r then w ⟨(i : ℕ), hi⟩ else 1) ∈ MonoidHom.ker (FreeGroup.lift g)
    by_cases hi : (i : ℕ) < r
    · rw [dite_eq_left hi]; exact h.1 ⟨(i : ℕ), hi⟩
    · rw [dite_eq_right hi]; exact Subgroup.one_mem _
  · intro Q _ _ hQ φ hφ
    refine h.2 Q hQ φ ?_
    intro j
    have hj : (j : ℕ) < r' := lt_of_lt_of_le j.isLt hr
    have heq : (fun i : Fin r' => if hi : (i : ℕ) < r then w ⟨(i : ℕ), hi⟩ else 1)
        ⟨(j : ℕ), hj⟩ = w j := by
      show (if hi : ((⟨(j : ℕ), hj⟩ : Fin r') : ℕ) < r then
        w ⟨((⟨(j : ℕ), hj⟩ : Fin r') : ℕ), hi⟩ else 1) = w j
      rw [dite_eq_left j.isLt]
    simpa only [heq] using hφ ⟨(j : ℕ), hj⟩

/-- **Residual `2`-finiteness of the presented group depends only on the normal closure of the
relators.**  If `⟪w'⟫ = ⟪w⟫` then `presentedGroup d r' w'` and `presentedGroup d r w` are
isomorphic, and the property `ResiduallyFiniteTwoGroup` is invariant under isomorphism
(`Work.ClassFieldTower.residuallyFiniteTwoGroup_of_mulEquiv`). -/
theorem residuallyFiniteTwoGroup_presented_congr {d r r' : ℕ} {w : Fin r → FreeGroup (Fin d)}
    {w' : Fin r' → FreeGroup (Fin d)}
    (h : Subgroup.normalClosure (Set.range w') = Subgroup.normalClosure (Set.range w))
    (hres : ResiduallyFiniteTwoGroup (presentedGroup d r w)) :
    ResiduallyFiniteTwoGroup (presentedGroup d r' w') :=
  residuallyFiniteTwoGroup_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq h) hres

theorem hasProTwoPresentationClosed_mono {F : Type*} [Field F] [NumberField F] {d r r' : ℕ}
    (h : Work.ShafarevichKoch.HasProTwoPresentationClosed F d r) (hr : r ≤ r') :
    Work.ShafarevichKoch.HasProTwoPresentationClosed F d r' := by
  obtain ⟨M, g, w, hdata, hdense, hres⟩ := h
  refine ⟨M, g, (fun i : Fin r' =>
    if hi : (i : ℕ) < r then w ⟨(i : ℕ), hi⟩ else 1), ?_, hdense, ?_⟩
  · exact pad_closedRelationData hdata hr
  · exact residuallyFiniteTwoGroup_presented_congr (pad_normalClosure hr w) hres

end Work.ShafarevichKoch
