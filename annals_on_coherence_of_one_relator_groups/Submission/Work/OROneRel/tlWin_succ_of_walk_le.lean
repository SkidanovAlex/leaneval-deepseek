import Mathlib
import Submission.Work.OROneRel.band_hnnConjMap_injective
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winE_mono
import Submission.Work.OROneRel.decorGetElemCover
import Submission.Work.OROneRel.decor_winE_shift
import Submission.Work.OROneRel.tlWin_map_conj_le_tlH
import Submission.Work.OROneRel.tlWin_succ_le_cherry
import Submission.Work.OROneRel.tlWin_succ_le_of_walk
import Submission.Work.OROneRel.tlWin_conn_path

namespace Work.OROneRel

universe u

/-! ## Assembly lemmas for `tlWin_succ_of_walk_le`

The main theorem is assembled from

* `tlWin_succ_le_of_walk` (the `≥` direction, walk bookkeeping: the conjugate of a loop of the
  window `[0,m]` by a weight-one element whose walk lies in `[0,m]` lands in `[0,m+1]`),
* `tlWin_conn_path` (existence of a path in the level graph on `[1,m]` from the level `1` to any
  level `t ∈ [1,m]`), and
* the "cherry" van Kampen lemma `tlWin_succ_le_cherry` together with the local Lemma
  `conn_handle_mem_tlWin` (the new handle `rα · a · b · rβ⁻¹`, read from level `1`, is a loop of the
  old window `[0,m]`).

`tlWin_succ_of_walk_le` itself is the equality. -/

/-- **A window walk concatenation.**  If `L₁` is a walk from level `i` all of whose edges lie in the
window `[lo,hi]` and `L₂` is a walk from the end level `i + lsig c L₁` with the same property, then
so is `L₁ ++ L₂`. -/
theorem decor_append_winE {α : Type u} (c : α → ℤ) {lo hi i : ℤ} (L₁ L₂ : List (α × Bool))
    (h1 : ∀ e ∈ decor c i L₁, coverEdge e ∈ winE c lo hi)
    (h2 : ∀ e ∈ decor c (i + lsig c L₁) L₂, coverEdge e ∈ winE c lo hi) :
    ∀ e ∈ decor c i (L₁ ++ L₂), coverEdge e ∈ winE c lo hi := by
  intro e he
  rw [decor_append] at he
  rcases List.mem_append.mp he with h | h
  · exact h1 e h
  · exact h2 e h

/-- **Monotonicity of the window subgroups** in the upper window bound. -/
theorem tlWin_mono_win (p q : ℕ) {m M : ℤ} (h : m ≤ M) : tlWin p q m ≤ tlWin p q M := by
  rw [tlWin_eq_closure_tlWinGen, tlWin_eq_closure_tlWinGen]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨L, hmk, hlsig, hwalk⟩
  exact Subgroup.subset_closure
    ⟨L, hmk, hlsig, fun e he => winE_mono (tlW p q) le_rfl h (hwalk e he)⟩

/-- The decoration of the two-letter block `a · b` (`a = of 0`, `b = of 1`) read at a level `α`. -/
theorem decor_pair_tlW (p q : ℕ) (α : ℤ) :
    decor (tlW p q) α [((0 : Fin 2), true), ((1 : Fin 2), true)] =
      [(((0 : Fin 2), α), true), (((1 : Fin 2), α + (q : ℤ)), true)] := by
  rw [decor_cons_l, decor_cons_l]
  simp only [linc, tlW, if_true, Fin.isValue, decor]

/-- The weight of the two-letter block `a · b` is `q - p`. -/
theorem lsig_pair_tlW (p q : ℕ) :
    lsig (tlW p q) [((0 : Fin 2), true), ((1 : Fin 2), true)] = (q : ℤ) - (p : ℤ) := by
  simp [lsig, tlW, sub_eq_add_neg]

/-- The class of the two-letter block is `of 0 * of 1`. -/
theorem mk_pair_tlW :
    FreeGroup.mk ([((0 : Fin 2), true), ((1 : Fin 2), true)] : List (Fin 2 × Bool)) =
      FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) := rfl

/-- **The handle of the new window, read from level `1`, is a loop of the old window.**  If `Rα`,
`Rβ` are walks of the level graph from the level `1` inside `[1,m]`, ending at the levels
`m+1-q`, `m+1-p` respectively, then the word `Rα · a · b · Rβ⁻¹` (read from the level `1`) is a
closed walk inside `[1, m+1]` of weight `0`; shifting it down by one level exhibits
`mk Rα · a · b · (mk Rβ)⁻¹` as an element of `tlWin p q m`. -/
theorem conn_handle_mem_tlWin (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) {m : ℤ}
    (hm1 : ((p : ℤ) + (q : ℤ) - 1) ≤ m) (hm2 : m + 1 ≤ (p : ℤ) * (q : ℤ))
    {Rα Rβ : List (Fin 2 × Bool)}
    (hα : lsig (tlW p q) Rα = m - (q : ℤ))
    (hβ : lsig (tlW p q) Rβ = m - (p : ℤ))
    (hwalkα : ∀ e ∈ decor (tlW p q) 1 Rα, coverEdge e ∈ winE (tlW p q) 1 m)
    (hwalkβ : ∀ e ∈ decor (tlW p q) 1 Rβ, coverEdge e ∈ winE (tlW p q) 1 m) :
    FreeGroup.mk Rα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
      (FreeGroup.mk Rβ)⁻¹ ∈ tlWin p q m := by
  classical
  set W : List (Fin 2 × Bool) :=
    Rα ++ [((0 : Fin 2), true), ((1 : Fin 2), true)] ++ FreeGroup.invRev Rβ with hW
  have hmkW : FreeGroup.mk W = FreeGroup.mk Rα * FreeGroup.of (0 : Fin 2) *
      FreeGroup.of (1 : Fin 2) * (FreeGroup.mk Rβ)⁻¹ := by
    rw [hW, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, mk_pair_tlW]
    group
  have hlsigW : lsig (tlW p q) W = 0 := by
    rw [hW, decor_lsig_append, decor_lsig_append, CoedgeBase.lsig_invRev,
      hα, hβ, lsig_pair_tlW]
    ring
  have hlevα : (1 : ℤ) + lsig (tlW p q) Rα = m + 1 - (q : ℤ) := by rw [hα]; ring
  have hpart1 : ∀ e ∈ decor (tlW p q) 1 Rα, coverEdge e ∈ winE (tlW p q) 1 (m + 1) :=
    fun e he => winE_mono (tlW p q) le_rfl (by omega) (hwalkα e he)
  have hpart2 : ∀ e ∈ decor (tlW p q) (1 + lsig (tlW p q) Rα)
      [((0 : Fin 2), true), ((1 : Fin 2), true)], coverEdge e ∈ winE (tlW p q) 1 (m + 1) := by
    rw [hlevα, decor_pair_tlW]
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · rw [mem_winE]
      simp only [coverEdge, tlW_zero]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
    · rw [mem_winE]
      simp only [coverEdge, tlW_one]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  have hpart12 : ∀ e ∈ decor (tlW p q) 1 (Rα ++ [((0 : Fin 2), true), ((1 : Fin 2), true)]),
      coverEdge e ∈ winE (tlW p q) 1 (m + 1) :=
    decor_append_winE (tlW p q) Rα [((0 : Fin 2), true), ((1 : Fin 2), true)] hpart1 hpart2
  have hpart3 : ∀ e ∈ decor (tlW p q)
      (1 + lsig (tlW p q) (Rα ++ [((0 : Fin 2), true), ((1 : Fin 2), true)]))
      (FreeGroup.invRev Rβ), coverEdge e ∈ winE (tlW p q) 1 (m + 1) := by
    have hlev3 : (1 : ℤ) + lsig (tlW p q) (Rα ++ [((0 : Fin 2), true), ((1 : Fin 2), true)])
        = 1 + lsig (tlW p q) Rβ := by
      rw [decor_lsig_append, hα, hβ, lsig_pair_tlW]; ring
    rw [hlev3, decor_invRev (tlW p q) 1 Rβ]
    intro e he
    obtain ⟨e', he'', hfe⟩ := List.mem_map.mp he
    have he' : e' ∈ decor (tlW p q) 1 Rβ := List.mem_reverse.mp he''
    rw [← hfe]
    exact winE_mono (tlW p q) le_rfl (by omega) (hwalkβ e' he')
  have hwalkW : ∀ e ∈ decor (tlW p q) 1 W, coverEdge e ∈ winE (tlW p q) 1 (m + 1) := by
    rw [hW]
    exact decor_append_winE (tlW p q) (Rα ++ [((0 : Fin 2), true), ((1 : Fin 2), true)])
      (FreeGroup.invRev Rβ) hpart12 hpart3
  have hshift := decor_winE_shift (tlW p q) 1 (-1) 1 (m + 1) W hwalkW
  have hshift0 : ∀ e ∈ decor (tlW p q) 0 W, coverEdge e ∈ winE (tlW p q) 0 m := by
    intro e he
    have h1 : e ∈ decor (tlW p q) ((1 : ℤ) + (-1)) W := by simpa using he
    have h2 := hshift e h1
    have h3 : ((1 : ℤ) + (-1)) = 0 := by norm_num
    have h4 : m + 1 + (-1) = m := by ring
    rwa [h3, h4] at h2
  rw [tlWin_eq_closure_tlWinGen, ← hmkW]
  exact Subgroup.subset_closure ⟨W, rfl, hlsigW, hshift0⟩

/-- **The window climb with an explicit deck element.**  For any element `σ` of weight one whose
walk lies in the window `[0,m]`, with `m ≥ p+q-1`, the window groups satisfy the recursion
`tlWin (m+1) = tlWin m ⊔ σ · tlWin m · σ⁻¹`.  (`≤` is van Kampen for the union
`Y[0,m+1] = Y[0,m] ∪ Y[1,m+1]` with the basepoint at level `1`; `≥` is monotonicity plus the fact
that the walk of `σ · w · σ⁻¹` lies in `[0,m+1]` for `w` a closed walk in `[0,m]`.)  A verified
counterexample for a `σ` whose walk leaves `[0,m]` is `(p,q,m) = (4,3,6)`, `σ = a³b²`, so the walk
hypothesis is not removable. -/
theorem tlWin_succ_of_walk_le (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    {σ : FreeGroup (Fin 2)} {m : ℤ}
    (hm1 : ((p : ℤ) + (q : ℤ) - 1) ≤ m)
    (hm2 : m + 1 ≤ (p : ℤ) * (q : ℤ))
    (hσ : Work.OROneRel.cohom (Work.OROneRel.tlW p q) σ = Multiplicative.ofAdd 1)
    (hwalk : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf σ),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 m) :
    Work.OROneRel.tlWin p q (m + 1) = Work.OROneRel.tlWin p q m ⊔
      (Work.OROneRel.tlWin p q m).map (MulAut.conj σ) := by
  have hσ1 : lsig (tlW p q) (wordOf σ) = 1 := by
    rw [CoedgeBase.lsig_wordOf, hσ]; rfl
  refine le_antisymm ?_ ?_
  · -- ### `≤`: van Kampen via the cherry plus the explicit handle
    obtain ⟨Rα, hRα, hwalkα⟩ :=
      tlWin_conn_path p q hp hq hcop hm1 hm2 (t := m + 1 - (q : ℤ)) (by omega) (by omega)
    obtain ⟨Rβ, hRβ, hwalkβ⟩ :=
      tlWin_conn_path p q hp hq hcop hm1 hm2 (t := m + 1 - (p : ℤ)) (by omega) (by omega)
    have hRα' : lsig (tlW p q) Rα = m - (q : ℤ) := by rw [hRα]; ring
    have hRβ' : lsig (tlW p q) Rβ = m - (p : ℤ) := by rw [hRβ]; ring
    -- connection paths `σ · rα`, `σ · rβ` from level `0` inside `[0,m]`
    have hα : ∃ L : List (Fin 2 × Bool), FreeGroup.mk L = σ * FreeGroup.mk Rα ∧
        lsig (tlW p q) L = m + 1 - (q : ℤ) ∧
        ∀ e ∈ decor (tlW p q) 0 L, coverEdge e ∈ winE (tlW p q) 0 m := by
      refine ⟨wordOf σ ++ Rα, ?_, ?_, ?_⟩
      · rw [← FreeGroup.mul_mk, mk_wordOf]
      · rw [decor_lsig_append, hσ1, hRα]; ring
      · refine decor_append_winE (tlW p q) (wordOf σ) Rα hwalk ?_
        rw [zero_add, hσ1]
        exact fun e he => winE_mono (tlW p q) (by norm_num) le_rfl (hwalkα e he)
    have hβ : ∃ L : List (Fin 2 × Bool), FreeGroup.mk L = σ * FreeGroup.mk Rβ ∧
        lsig (tlW p q) L = m + 1 - (p : ℤ) ∧
        ∀ e ∈ decor (tlW p q) 0 L, coverEdge e ∈ winE (tlW p q) 0 m := by
      refine ⟨wordOf σ ++ Rβ, ?_, ?_, ?_⟩
      · rw [← FreeGroup.mul_mk, mk_wordOf]
      · rw [decor_lsig_append, hσ1, hRβ]; ring
      · refine decor_append_winE (tlW p q) (wordOf σ) Rβ hwalk ?_
        rw [zero_add, hσ1]
        exact fun e he => winE_mono (tlW p q) (by norm_num) le_rfl (hwalkβ e he)
    refine le_trans (tlWin_succ_le_cherry p q hp hq hcop hm1 hα hβ) (sup_le le_sup_left ?_)
    refine (Subgroup.closure_le _).mpr ?_
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    refine Subgroup.mem_sup_right (Subgroup.mem_map.mpr
      ⟨FreeGroup.mk Rα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
          (FreeGroup.mk Rβ)⁻¹,
        conn_handle_mem_tlWin p q hp hq hm1 hm2 hRα' hRβ' hwalkα hwalkβ, ?_⟩)
    change σ * (FreeGroup.mk Rα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
          (FreeGroup.mk Rβ)⁻¹) * σ⁻¹
      = σ * FreeGroup.mk Rα * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
          (σ * FreeGroup.mk Rβ)⁻¹
    group
  · -- ### `≥`: walk bookkeeping
    exact tlWin_succ_le_of_walk p q hσ hwalk

end Work.OROneRel
