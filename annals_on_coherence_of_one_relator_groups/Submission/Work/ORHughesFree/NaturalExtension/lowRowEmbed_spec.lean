import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.TruncDefect

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- The `finProdFinEquiv` decomposition of an element of `Fin (n * i)` as the pair
`(q.divNat, q.modNat)`; this is the inverse identity of `finProdFinEquiv_symm_apply`. -/
lemma finProdFinEquiv_divNat_modNat {n i : ℕ} (q : Fin (n * i)) :
    finProdFinEquiv (q.divNat, q.modNat) = q := by
  rw [← finProdFinEquiv_symm_apply q, Equiv.apply_symm_apply]

/-- The `divNat` (block index) of the low row embedding is the block index of the source index. -/
lemma lowRowEmbed_divNat {n a i : ℕ} (k : Fin (n * min a i)) :
    (lowRowEmbed n a i k).divNat = k.divNat := by
  simp [lowRowEmbed, Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_fst]

/-- The `modNat` (degree) of the low row embedding is the degree of the source index. -/
lemma lowRowEmbed_modNat {n a i : ℕ} (k : Fin (n * min a i)) :
    ((lowRowEmbed n a i k).modNat : ℕ) = (k.modNat : ℕ) := by
  simp [lowRowEmbed, Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_snd]

/-- The underlying value of the low row embedding:
`(k.modNat : ℕ) + i * (k.divNat : ℕ)`. -/
lemma lowRowEmbed_val {n a i : ℕ} (k : Fin (n * min a i)) :
    ((lowRowEmbed n a i k : Fin (n * i)) : ℕ) = (k.modNat : ℕ) + i * (k.divNat : ℕ) := by
  show ((finProdFinEquiv _ : Fin (n * i)) : ℕ) = _
  simp [finProdFinEquiv]

theorem lowRowEmbed_spec (n a i : ℕ) :
    Function.Injective (lowRowEmbed n a i) ∧
      ∀ q : Fin (n * i), q ∈ Set.range (lowRowEmbed n a i) ↔ (q.modNat : ℕ) < a := by
  constructor
  · intro k k' h
    have hd : k.divNat = k'.divNat := by
      rw [← lowRowEmbed_divNat k, ← lowRowEmbed_divNat k', h]
    have hm : k.modNat = k'.modNat := by
      refine Fin.ext ?_
      rw [← lowRowEmbed_modNat k, ← lowRowEmbed_modNat k', h]
    calc k = finProdFinEquiv (k.divNat, k.modNat) := (finProdFinEquiv_divNat_modNat k).symm
      _ = finProdFinEquiv (k'.divNat, k'.modNat) := by rw [hd, hm]
      _ = k' := finProdFinEquiv_divNat_modNat k'
  · intro q
    constructor
    · rintro ⟨k, rfl⟩
      rw [lowRowEmbed_modNat k]
      exact lt_of_lt_of_le k.modNat.isLt (min_le_left a i)
    · intro h
      refine ⟨finProdFinEquiv (q.divNat,
        ⟨(q.modNat : ℕ), Nat.lt_min.mpr ⟨h, q.modNat.isLt⟩⟩), ?_⟩
      have hdiv : (finProdFinEquiv (q.divNat,
          ⟨(q.modNat : ℕ), Nat.lt_min.mpr ⟨h, q.modNat.isLt⟩⟩) :
            Fin (n * min a i)).divNat = q.divNat :=
        Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_fst _ _
      have hmod : ((finProdFinEquiv (q.divNat,
          ⟨(q.modNat : ℕ), Nat.lt_min.mpr ⟨h, q.modNat.isLt⟩⟩) :
            Fin (n * min a i)).modNat : ℕ) = (q.modNat : ℕ) := by
        rw [Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_snd]
      have hmod' : (lowRowEmbed n a i (finProdFinEquiv (q.divNat,
          ⟨(q.modNat : ℕ), Nat.lt_min.mpr ⟨h, q.modNat.isLt⟩⟩))).modNat = q.modNat := by
        refine Fin.ext ?_
        rw [lowRowEmbed_modNat, hmod]
      calc lowRowEmbed n a i (finProdFinEquiv (q.divNat,
              ⟨(q.modNat : ℕ), Nat.lt_min.mpr ⟨h, q.modNat.isLt⟩⟩))
          = finProdFinEquiv ((lowRowEmbed n a i (finProdFinEquiv (q.divNat,
              ⟨(q.modNat : ℕ), Nat.lt_min.mpr ⟨h, q.modNat.isLt⟩⟩))).divNat,
              (lowRowEmbed n a i (finProdFinEquiv (q.divNat,
              ⟨(q.modNat : ℕ), Nat.lt_min.mpr ⟨h, q.modNat.isLt⟩⟩))).modNat) :=
            (finProdFinEquiv_divNat_modNat _).symm
        _ = finProdFinEquiv (q.divNat, q.modNat) := by
              rw [lowRowEmbed_divNat, hdiv, hmod']
        _ = q := finProdFinEquiv_divNat_modNat q

end Work.ORHughesFree.NaturalExtension
