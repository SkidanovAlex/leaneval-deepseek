import Mathlib
import Submission.Work.Pi6.MSSK.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSSK

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

set_option autoImplicit false

/-!
# `altFacesSum`

For a simplex `α` of the standard simplex `Δ[s]` of dimension `s+1`, the alternating sum of the
indicators of "the `i`-th face of `α` is the top simplex" vanishes:

`∑ i : Fin (s+2), (-1)^i • [δ i α = topS s] = 0`   (in any commutative ring `R`).

Equivalently, the `s`-cochain on `Δ[s]` which is `1` on the top simplex and `0` elsewhere is a
cocycle — which is what the cap-product/cocycle computation of `thetaTop` needs.

The proof is purely combinatorial.  Writing `α` under the Yoneda equivalence as a monotone map
`f : ⦋s+1⦌ ⟶ ⦋s⦌`, the `i`-th face of `α` is the top simplex iff `f ∘ δ i = id`, i.e. iff

* `f j = j` for `j < i` and
* `f j = j - 1` for `j > i`   (`Cut f i`).

The set of such `i` is either empty or a pair of consecutive indices `{c, c+1}`: two such indices
differ by at most one (`altCut_dist`), and such an index is never alone (`altCut_succ_or_pred`,
using the minimality of the smallest one).  The contributions `(-1)^c + (-1)^(c+1)` cancel.
-/

noncomputable section

/-- The "cut form" of the condition `f ∘ δ i = id`: `f` fixes everything below `m` and shifts
everything above `m` down by one. -/
def altCut {s : ℕ} (a : Fin (s+2) →o Fin (s+1)) (m : ℕ) : Prop :=
  (∀ j : Fin (s+2), j.val < m → (a j).val = j.val) ∧
  (∀ j : Fin (s+2), m < j.val → (a j).val + 1 = j.val)

/-- The `Fin.succAbove` form and the cut form of the condition agree. -/
lemma altCut_iff_succAbove {s : ℕ} (a : Fin (s+2) →o Fin (s+1)) (i : Fin (s+2)) :
    (∀ k : Fin (s+1), a (Fin.succAbove i k) = k) ↔ altCut a i.val := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j hj
      have hjl : j.val < s + 1 := lt_of_lt_of_le hj (Nat.le_of_lt_succ i.isLt)
      have hlt : (⟨j.val, hjl⟩ : Fin (s+1)).castSucc < i := by
        rw [Fin.lt_def, Fin.val_castSucc]; exact hj
      have hs : Fin.succAbove i (⟨j.val, hjl⟩ : Fin (s+1)) = j := by
        rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
        apply Fin.ext; rfl
      have hh := congrArg Fin.val (h ⟨j.val, hjl⟩)
      rw [hs] at hh
      exact hh
    · intro j hj
      have hjne : j ≠ 0 := by intro h0; rw [h0] at hj; exact Nat.not_lt_zero _ hj
      have hge : i ≤ (j.pred hjne).castSucc := by
        rw [Fin.le_def, Fin.val_castSucc, Fin.val_pred]; omega
      have hs : Fin.succAbove i (j.pred hjne) = j := by
        rw [Fin.succAbove_of_le_castSucc _ _ hge, Fin.succ_pred]
      have hh := congrArg Fin.val (h (j.pred hjne))
      rw [hs, Fin.val_pred] at hh
      omega
  · intro h k
    rcases lt_or_ge k.val i.val with hk | hk
    · have hlt : k.castSucc < i := by rw [Fin.lt_def, Fin.val_castSucc]; exact hk
      rw [Fin.succAbove_of_castSucc_lt _ _ hlt]
      apply Fin.ext
      have hh := h.1 k.castSucc (by rw [Fin.val_castSucc]; exact hk)
      rwa [Fin.val_castSucc] at hh
    · have hle : i ≤ k.castSucc := by rw [Fin.le_def, Fin.val_castSucc]; exact hk
      rw [Fin.succAbove_of_le_castSucc _ _ hle]
      apply Fin.ext
      have hh := h.2 k.succ (by rw [Fin.val_succ]; omega)
      have hh2 : (a (k.succ)).val + 1 = k.val + 1 := by rw [hh, Fin.val_succ]
      omega

/-- A cut index never exceeds `s+1`. -/
lemma altCut_le {s : ℕ} (a : Fin (s+2) →o Fin (s+1)) {m : ℕ} (h : altCut a m) : m ≤ s + 1 := by
  by_contra hm
  have hj : (Fin.last (s+1)).val < m := by simp [Fin.last]; omega
  have h1 := h.1 (Fin.last (s+1)) hj
  have h2 : (a (Fin.last (s+1))).val < s + 1 := (a (Fin.last (s+1))).isLt
  simp [Fin.last] at h1
  omega

/-- Two cut indices differ by at most one. -/
lemma altCut_dist {s : ℕ} (a : Fin (s+2) →o Fin (s+1)) {m m' : ℕ} (h : altCut a m)
    (h' : altCut a m') (hmm : m + 2 ≤ m') : False := by
  have hm : m ≤ s + 1 := altCut_le a h
  have hm' : m' ≤ s + 1 := altCut_le a h'
  have hi : m + 1 < s + 2 := by omega
  have h1 : (a (⟨m+1, hi⟩ : Fin (s+2))).val + 1 = m + 1 :=
    h.2 ⟨m+1, hi⟩ (by rw [Fin.val_mk]; omega)
  have h2 : (a (⟨m+1, hi⟩ : Fin (s+2))).val = m + 1 :=
    h'.1 ⟨m+1, hi⟩ (by rw [Fin.val_mk]; omega)
  omega

/-- A cut index is never alone: one of its neighbours is again a cut index. -/
lemma altCut_succ_or_pred {s : ℕ} (a : Fin (s+2) →o Fin (s+1)) {m : ℕ} (h : altCut a m) :
    altCut a (m+1) ∨ (1 ≤ m ∧ altCut a (m-1)) := by
  have hm : m ≤ s + 1 := altCut_le a h
  have hi : m < s + 2 := by omega
  have hA : (a ⟨m,hi⟩).val ≤ m := by
    rcases lt_or_ge m (s+1) with hlt | hle
    · have hi2 : m + 1 < s + 2 := by omega
      have h2 : (a ⟨m+1,hi2⟩).val = m := by
        have hh : (a ⟨m+1,hi2⟩).val + 1 = m + 1 := h.2 ⟨m+1,hi2⟩ (by simp)
        omega
      have hmono : (a ⟨m,hi⟩).val ≤ (a ⟨m+1,hi2⟩).val := a.monotone (by simp [Fin.le_def])
      omega
    · have hms : m = s + 1 := by omega
      have := (a ⟨m,hi⟩).isLt
      omega
  have hB : m - 1 ≤ (a ⟨m,hi⟩).val := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · omega
    · have hi2 : m - 1 < s + 2 := by omega
      have h2 : (a ⟨m-1,hi2⟩).val = m - 1 := h.1 ⟨m-1,hi2⟩ (by rw [Fin.val_mk]; omega)
      have hmono : (a ⟨m-1,hi2⟩).val ≤ (a ⟨m,hi⟩).val := a.monotone (by simp [Fin.le_def])
      omega
  have key : (a ⟨m,hi⟩).val = m ∨ (1 ≤ m ∧ (a ⟨m,hi⟩).val = m - 1) := by omega
  rcases key with hEq | ⟨hm1, hEq⟩
  · left
    refine ⟨?_, ?_⟩
    · intro j hj
      rcases lt_or_eq_of_le (show j.val ≤ m by omega) with hj' | hj'
      · exact h.1 j (by omega)
      · have hji : j = ⟨m,hi⟩ := Fin.ext hj'
        rw [hji, hEq]
    · intro j hj
      exact h.2 j (by omega)
  · right
    refine ⟨hm1, ?_, ?_⟩
    · intro j hj
      exact h.1 j (by omega)
    · intro j hj
      rcases eq_or_lt_of_le (show m ≤ j.val by omega) with hjm | hjm
      · have hji : j = ⟨m,hi⟩ := Fin.ext hjm.symm
        rw [hji]
        omega
      · exact h.2 j (by omega)

/-- The alternating sum of the indicators of the cut condition vanishes. -/
lemma altCut_sum (R : Type) [CommRing R] {s : ℕ} (a : Fin (s+2) →o Fin (s+1))
    [DecidablePred (altCut a)] :
    (∑ i : Fin (s+2), ((-1:R)^(i:ℕ)) * (if altCut a i.val then (1:R) else 0)) = 0 := by
  have h1 : (∑ i : Fin (s+2), ((-1:R)^(i:ℕ)) * (if altCut a i.val then (1:R) else 0))
      = ∑ m ∈ Finset.range (s+2), (-1:R)^m * (if altCut a m then (1:R) else 0) :=
    Fin.sum_univ_eq_sum_range (fun m => (-1:R)^m * (if altCut a m then (1:R) else 0)) (s+2)
  rw [h1]
  have h2 : (∑ m ∈ Finset.range (s+2), (-1:R)^m * (if altCut a m then (1:R) else 0))
      = ∑ m ∈ (Finset.range (s+2)).filter (fun m => altCut a m), (-1:R)^m := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun m _ => by by_cases hc : altCut a m <;> simp [hc])
  rw [h2]
  rcases ((Finset.range (s+2)).filter (fun m => altCut a m)).eq_empty_or_nonempty with hT | hT
  · rw [hT, Finset.sum_empty]
  · have hiT : ((Finset.range (s+2)).filter (fun m => altCut a m)).min' hT
        ∈ (Finset.range (s+2)).filter (fun m => altCut a m) := Finset.min'_mem _ _
    set i := ((Finset.range (s+2)).filter (fun m => altCut a m)).min' hT with hidef
    have hiC : altCut a i := (Finset.mem_filter.mp hiT).2
    have hile : i ≤ s + 1 := altCut_le a hiC
    have hsucc : altCut a (i+1) := by
      rcases altCut_succ_or_pred a hiC with hh | ⟨hm1, hh⟩
      · exact hh
      · have hmem : i - 1 ∈ (Finset.range (s+2)).filter (fun m => altCut a m) :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hh⟩
        have := Finset.min'_le _ (i-1) hmem
        omega
    have heq : (Finset.range (s+2)).filter (fun m => altCut a m) = {i, i+1} := by
      apply Finset.ext
      intro j
      constructor
      · intro hj
        have hjC : altCut a j := (Finset.mem_filter.mp hj).2
        have hji : i ≤ j := Finset.min'_le _ j hj
        have hnd : ¬ (i + 2 ≤ j) := fun hc => altCut_dist a hiC hjC hc
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      · intro hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hiC⟩
        · have hile2 : i + 1 ≤ s + 1 := altCut_le a hsucc
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hsucc⟩
    rw [heq, Finset.sum_pair (by omega : i ≠ i+1), pow_succ]
    ring

/-- The morphism equation `δ i ≫ f = id` is the pointwise condition `f (succAbove i k) = k`. -/
lemma mor_eq_id_iff {s : ℕ} (f : ⦋s+1⦌ ⟶ ⦋s⦌) (i : Fin (s+2)) :
    SimplexCategory.δ i ≫ f = 𝟙 ⦋s⦌ ↔ ∀ k : Fin (s+1), f.toOrderHom (Fin.succAbove i k) = k := by
  constructor
  · intro h k
    have h2 : f.toOrderHom.comp (SimplexCategory.δ i).toOrderHom = OrderHom.id := by
      rw [← SimplexCategory.comp_toOrderHom, h]
      rfl
    have h3 := DFunLike.congr_fun h2 k
    simpa [SimplexCategory.δ, SimplexCategory.mkHom, Fin.succAboveOrderEmb] using h3
  · intro h
    apply SimplexCategory.Hom.ext
    rw [SimplexCategory.comp_toOrderHom]
    ext k
    exact congrArg Fin.val (h k)

theorem altFacesSum (R : Type) [CommRing R] {s : ℕ}
    (α : (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}).obj
        (Opposite.op (SimplexCategory.mk (s + 1)))) :
    (∑ i : Fin (s + 2), ((-1 : R) ^ (i : ℕ)) *
      (if CategoryTheory.SimplicialObject.δ
            (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) i α
        = Work.Pi6.MSSK.topS s then (1 : R) else 0)) = 0 := by
  classical
  set f : ⦋s+1⦌ ⟶ ⦋s⦌ := SSet.stdSimplex.objEquiv α with hf
  have hα : SSet.stdSimplex.objEquiv.symm f = α := by
    rw [hf]; exact Equiv.symm_apply_apply _ α
  have hkey : ∀ i : Fin (s+2),
      (CategoryTheory.SimplicialObject.δ
          (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) i α
        = Work.Pi6.MSSK.topS s)
      ↔ altCut f.toOrderHom i.val := by
    intro i
    have h1 : CategoryTheory.SimplicialObject.δ
          (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) i α
        = SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i ≫ f) := by
      rw [← hα]
      exact SSet.stdSimplex.δ_objEquiv_symm_apply (m := SimplexCategory.mk s) f i
    rw [h1]
    have h2 : (SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ i ≫ f)
          = Work.Pi6.MSSK.topS s)
        ↔ (SimplexCategory.δ i ≫ f = 𝟙 ⦋s⦌) := by
      rw [show Work.Pi6.MSSK.topS s = SSet.stdSimplex.objEquiv.symm (𝟙 ⦋s⦌) from rfl]
      exact (SSet.stdSimplex.objEquiv (n := SimplexCategory.mk s) (m := op ⦋s⦌)).symm.injective.eq_iff
    rw [h2, mor_eq_id_iff, altCut_iff_succAbove]
  have hsum : (∑ i : Fin (s + 2), ((-1 : R) ^ (i : ℕ)) *
        (if CategoryTheory.SimplicialObject.δ
              (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) i α
          = Work.Pi6.MSSK.topS s then (1 : R) else 0))
      = ∑ i : Fin (s + 2), ((-1 : R) ^ (i : ℕ)) *
        (if altCut f.toOrderHom i.val then (1 : R) else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    by_cases h : (CategoryTheory.SimplicialObject.δ
              (SSet.stdSimplex.obj (SimplexCategory.mk s) : SSet.{0}) i α
          = Work.Pi6.MSSK.topS s)
    · rw [if_pos h, if_pos ((hkey i).mp h)]
    · rw [if_neg h, if_neg (fun hc => h ((hkey i).mpr hc))]
  rw [hsum]
  exact altCut_sum R f.toOrderHom

end

end Work.Pi6.MSSK
