import Mathlib
import Submission.Work.WilE3.Frame.CutSys

namespace Work.WilE3.Frame

open WilkiesDesign.E

/-- Reindexing identity behind the degree bookkeeping of the cut system: summing an arbitrary
commutative-monoid valued function over `Fin k` splits into the three blocks carried by the rows
`rowH` (`j` rows), `rowL` (`k - j - 1` rows) and `rowF` (the last row). -/
lemma sum_univ_row_decomp {k j : ℕ} {M : Type*} [AddCommMonoid M]
    (hjk : j < k) (g : Fin k → M) :
    ∑ i : Fin k, g i
      = ∑ a : Fin j, g (rowH hjk a) + ∑ b : Fin (k - j - 1), g (rowL hjk b) + g (rowF hjk) := by
  have hinjH : Function.Injective (rowH (k := k) (j := j) hjk) := by
    intro a b hab
    simp only [rowH, Fin.mk.injEq] at hab
    exact Fin.ext hab
  have hinjL : Function.Injective (rowL (k := k) (j := j) hjk) := by
    intro a b hab
    simp only [rowL, Fin.mk.injEq] at hab
    exact Fin.ext (by omega)
  set SH : Finset (Fin k) := Finset.univ.image (rowH (k := k) (j := j) hjk) with hSH
  set SL : Finset (Fin k) := Finset.univ.image (rowL (k := k) (j := j) hjk) with hSL
  have hmemH : ∀ a : Fin j, rowH hjk a ∈ SH := by
    intro a; rw [hSH]; exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hmemL : ∀ b : Fin (k - j - 1), rowL hjk b ∈ SL := by
    intro b; rw [hSL]; exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩
  -- The three blocks cover every row.
  have hcover : SH ∪ SL ∪ ({rowF hjk} : Finset (Fin k)) = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro i
    rcases cutSys_cases hjk i with ⟨a, rfl⟩ | ⟨b, rfl⟩ | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hmemH a))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hmemL b))
    · exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  -- The blocks are pairwise disjoint.
  have hdisj1 : Disjoint SH SL := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [hSH, Finset.mem_image] at hx
    rw [hSL, Finset.mem_image] at hx'
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, hb⟩ := hx'
    simp only [rowL, rowH, Fin.mk.injEq] at hb
    omega
  have hdisj2 : Disjoint (SH ∪ SL) ({rowF hjk} : Finset (Fin k)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_singleton] at hx'
    subst hx'
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · rw [hSH, Finset.mem_image] at hx
      obtain ⟨a, -, ha⟩ := hx
      simp only [rowH, rowF, Fin.mk.injEq] at ha
      omega
    · rw [hSL, Finset.mem_image] at hx
      obtain ⟨b, -, hb⟩ := hx
      simp only [rowL, rowF, Fin.mk.injEq] at hb
      omega
  have key : ∑ i : Fin k, g i = ∑ i ∈ SH, g i + ∑ i ∈ SL, g i + g (rowF hjk) := by
    rw [← hcover]
    rw [Finset.sum_union hdisj2, Finset.sum_union hdisj1, Finset.sum_singleton]
  have hSHsum : ∑ i ∈ SH, g i = ∑ a : Fin j, g (rowH hjk a) := by
    rw [hSH, Finset.sum_image]
    intro a _ b _ hab; exact hinjH hab
  have hSLsum : ∑ i ∈ SL, g i = ∑ b : Fin (k - j - 1), g (rowL hjk b) := by
    rw [hSL, Finset.sum_image]
    intro a _ b _ hab; exact hinjL hab
  rw [key, hSHsum, hSLsum]

theorem cutSys_atomDeg_sum {k r j : ℕ} (hjk : j < k)
    (h : Fin j → WilkiesDesign.E.EAPoly k r) (L : Fin (k - j - 1) → WilkiesDesign.E.EAPoly k r)
    (f : WilkiesDesign.E.EAPoly k r) :
    (∑ i : Fin k, WilkiesDesign.E.atomDeg (Work.WilE3.Frame.cutSys h L f i))
      = (∑ a : Fin j, WilkiesDesign.E.atomDeg (h a))
        + (∑ b : Fin (k - j - 1), WilkiesDesign.E.atomDeg (L b))
        + WilkiesDesign.E.atomDeg f := by
  rw [sum_univ_row_decomp (hjk := hjk) (g := fun i => WilkiesDesign.E.atomDeg (cutSys h L f i))]
  simp only [cutSys_rowH, cutSys_rowL, cutSys_rowF]

end Work.WilE3.Frame
