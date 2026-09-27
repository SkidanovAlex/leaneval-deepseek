import Mathlib
import Submission.Work.EKLRelCross.flower

/-!
# `Work.EKLProd.atom_sup_generateFrom` — the atom of a join of σ-algebras

For any two σ-algebras `m₁ m₂` on `X₃` the atom (intersection of all measurable sets
containing `x`) of the join is the intersection of the atoms:

`[x]_{m₁ ⊔ m₂} = [x]_{m₁} ∩ [x]_{m₂}`.

The inclusion `⊆` is monotonicity of the atom in the σ-algebra
(`m ≤ m'` ⟹ `[x]_{m'} ⊆ [x]_{m}`).  For the reverse inclusion, two points lie in the same
atom of `m` precisely when no `m`-measurable set separates them
(`mem_atom_iff`); the family of sets which do not separate two given points is itself a
σ-algebra, so if `m₁` and `m₂` both fail to separate them, neither does their join.
-/

namespace Work.EKLProd

open Work.EKLContract
open scoped MeasureTheory

/-- `y` lies in the atom of `x` for `m` iff no `m`-measurable set separates `x` and `y`. -/
theorem mem_atom_iff (m : MeasurableSpace X3) (x y : X3) :
    y ∈ atom m x ↔ ∀ s, MeasurableSet[m] s → (x ∈ s ↔ y ∈ s) := by
  constructor
  · intro hy s hs
    refine ⟨fun hx => ?_, fun hys => ?_⟩
    · rw [atom, Set.mem_sInter] at hy
      exact hy s ⟨hs, hx⟩
    · by_contra hxs
      rw [atom, Set.mem_sInter] at hy
      exact (hy sᶜ ⟨hs.compl, hxs⟩) hys
  · intro h
    rw [atom, Set.mem_sInter]
    rintro s ⟨hs, hxs⟩
    exact (h s hs).mp hxs

/-- The atom is antitone in the σ-algebra: a finer σ-algebra gives a smaller atom. -/
theorem atom_mono {m m' : MeasurableSpace X3} (h : m ≤ m') (x : X3) :
    atom m' x ⊆ atom m x := by
  intro y hy
  rw [mem_atom_iff] at hy ⊢
  exact fun s hs => hy s (h s hs)

/-- `[x]_{m₁ ⊔ m₂} ⊆ [x]_{m₁} ∩ [x]_{m₂}`. -/
theorem atom_sup_subset (m₁ m₂ : MeasurableSpace X3) (x : X3) :
    atom (m₁ ⊔ m₂) x ⊆ atom m₁ x ∩ atom m₂ x := by
  intro y hy
  exact ⟨atom_mono le_sup_left x hy, atom_mono le_sup_right x hy⟩

/-- `[x]_{m₁} ∩ [x]_{m₂} ⊆ [x]_{m₁ ⊔ m₂}`: the sets which do not separate `x` and `y` form a
σ-algebra, so it suffices that both `m₁` and `m₂` consist of such sets. -/
theorem atom_sup_supset (m₁ m₂ : MeasurableSpace X3) (x : X3) :
    atom m₁ x ∩ atom m₂ x ⊆ atom (m₁ ⊔ m₂) x := by
  intro y hy
  obtain ⟨hy₁, hy₂⟩ := hy
  rw [mem_atom_iff] at hy₁ hy₂ ⊢
  let F : MeasurableSpace X3 :=
    { MeasurableSet' := fun s => x ∈ s ↔ y ∈ s
      measurableSet_empty := by simp
      measurableSet_compl := by
        intro s hs
        simp only [Set.mem_compl_iff]
        exact hs.not
      measurableSet_iUnion := by
        intro f hf
        simp only [Set.mem_iUnion]
        exact exists_congr fun i => hf i }
  have hm₁ : m₁ ≤ F := fun s hs => hy₁ s hs
  have hm₂ : m₂ ≤ F := fun s hs => hy₂ s hs
  exact sup_le hm₁ hm₂

theorem atom_sup_generateFrom (G₁ G₂ : Set (Set Work.EKLContract.X3)) (x : Work.EKLContract.X3) :
    Work.EKLContract.atom
        (MeasurableSpace.generateFrom G₁ ⊔ MeasurableSpace.generateFrom G₂) x =
      Work.EKLContract.atom (MeasurableSpace.generateFrom G₁) x ∩
        Work.EKLContract.atom (MeasurableSpace.generateFrom G₂) x :=
  Set.Subset.antisymm (atom_sup_subset _ _ x) (atom_sup_supset _ _ x)

end Work.EKLProd
