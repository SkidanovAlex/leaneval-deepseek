import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winBandDefs
import Submission.Work.OROneRel.gauge_nontrivial_bound

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **A step of the allowed shape is realised by a letter.**  If `c x0 = ±A` and `c y0 = ±B` and
`s ∈ {A, -A, B, -B}` then some letter `(a,b)` has increment `linc c (a,b) = s`. -/
theorem exists_linc_eq (c : α → ℤ) (x0 y0 : α) (A B : ℤ)
    (hx0 : c x0 = A ∨ c x0 = -A) (hy0 : c y0 = B ∨ c y0 = -B)
    (s : ℤ) (hs : s = A ∨ s = -A ∨ s = B ∨ s = -B) :
    ∃ p : α × Bool, linc c p = s := by
  rcases hx0 with hx | hx
  · rcases hs with h | h | h | h
    · exact ⟨(x0, true), by simp [linc, h, hx]⟩
    · exact ⟨(x0, false), by simp [linc, h, hx]⟩
    · rcases hy0 with hy | hy
      · exact ⟨(y0, true), by simp [linc, h, hy]⟩
      · exact ⟨(y0, false), by simp [linc, h, hy]⟩
    · rcases hy0 with hy | hy
      · exact ⟨(y0, false), by simp [linc, h, hy]⟩
      · exact ⟨(y0, true), by simp [linc, h, hy]⟩
  · rcases hs with h | h | h | h
    · exact ⟨(x0, false), by simp [linc, h, hx]⟩
    · exact ⟨(x0, true), by simp [linc, h, hx]⟩
    · rcases hy0 with hy | hy
      · exact ⟨(y0, true), by simp [linc, h, hy]⟩
      · exact ⟨(y0, false), by simp [linc, h, hy]⟩
    · rcases hy0 with hy | hy
      · exact ⟨(y0, false), by simp [linc, h, hy]⟩
      · exact ⟨(y0, true), by simp [linc, h, hy]⟩

/-- The weight of a word is the sum of the increments of its letters. -/
theorem lsig_eq_sum_map_linc (c : α → ℤ) (L : List (α × Bool)) :
    lsig c L = (L.map (linc c)).sum := rfl

/-- The level list of a word is the scan of its increments. -/
theorem lv_eq_scanl_map_linc (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    lv c i L = (L.map (linc c)).scanl (fun a b => a + b) i := rfl

/-- **An edge of the decorated word lies in the window as soon as the levels of the walk do.** -/
theorem coverEdge_mem_winE_of_lv (c : α → ℤ) (i lo hi : ℤ) (L : List (α × Bool))
    (h : ∀ l ∈ lv c i L, lo ≤ l ∧ l ≤ hi) :
    ∀ q ∈ decor c i L, coverEdge q ∈ winE c lo hi := by
  intro q hq
  rw [coverEdge_mem_winE_iff]
  exact ⟨(h _ (coverSrc_mem_lv c i L hq)).1, (h _ (coverSrc_mem_lv c i L hq)).2,
    (h _ (coverTgt_mem_lv c i L hq)).1, (h _ (coverTgt_mem_lv c i L hq)).2⟩

theorem exists_word_of_confined_steps {α : Type u} [DecidableEq α] (c : α → ℤ) (x0 y0 : α)
    (A B : ℤ) (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hAB : A ≠ B)
    (hx0 : c x0 = A ∨ c x0 = -A) (hy0 : c y0 = B ∨ c y0 = -B)
    (ss : List ℤ) (hstep : ∀ s ∈ ss, s = A ∨ s = -A ∨ s = B ∨ s = -B) (lo hi : ℤ)
    (hband : ∀ l ∈ ss.scanl (fun a b => a + b) 0, lo ≤ l ∧ l ≤ hi) :
    ∃ L : List (α × Bool), Work.OROneRel.lsig c L = ss.sum ∧
      ∀ q ∈ Work.OROneRel.decor c 0 L, Work.OROneRel.coverEdge q ∈ Work.OROneRel.winE c lo hi := by
  classical
  -- choose, for every step of `ss`, a letter of `α` realising it
  let f : {s // s ∈ ss} → α × Bool :=
    fun x => Classical.choose (exists_linc_eq c x0 y0 A B hx0 hy0 x.1 (hstep x.1 x.2))
  have hf : ∀ x : {s // s ∈ ss}, linc c (f x) = x.1 :=
    fun x => Classical.choose_spec (exists_linc_eq c x0 y0 A B hx0 hy0 x.1 (hstep x.1 x.2))
  -- the increments of the word are exactly the steps
  have hmap : (ss.attach.map f).map (linc c) = ss := by
    rw [List.map_map]
    have hfun : (linc c) ∘ f = (Subtype.val : {s // s ∈ ss} → ℤ) := by
      funext x
      exact hf x
    rw [hfun]
    exact List.attach_map_subtype_val ss
  refine ⟨ss.attach.map f, ?_, ?_⟩
  · rw [lsig_eq_sum_map_linc, hmap]
  · have hlv : lv c 0 (ss.attach.map f) = ss.scanl (fun a b => a + b) 0 := by
      rw [lv_eq_scanl_map_linc, hmap]
    refine coverEdge_mem_winE_of_lv c 0 lo hi (ss.attach.map f) (fun l hl => ?_)
    rw [hlv] at hl
    exact hband l hl

end Work.OROneRel
