import Mathlib.GroupTheory.Complement
import Mathlib.Order.CompletePartialOrder

namespace Commons.PeriodicTiling

open scoped Pointwise

theorem rigid_partition_concat_solvable
    {G : Type*} [AddCommGroup G] {M N : ℕ}
    (F : Fin M → Set G) (A : Set G)
    (E : Fin M → Set (ZMod N))
    (hEcover : ∀ x : ZMod N, ∃ i : Fin M, x ∈ E i)
    (hEdisj : ∀ i j : Fin M, i ≠ j → Disjoint (E i) (E j))
    (hA : ∀ i : Fin M, AddSubgroup.IsComplement A (F i)) :
    AddSubgroup.IsComplement (A ×ˢ ({0} : Set (ZMod N)))
      {x : G × ZMod N | ∃ i : Fin M, x.1 ∈ F i ∧ x.2 ∈ E i} := by
  rw [AddSubgroup.isComplement_iff_existsUnique]
  intro gz
  rcases gz with ⟨g, z⟩
  obtain ⟨i, hzi⟩ := hEcover z
  obtain ⟨⟨⟨a, haA⟩, ⟨f, hfF⟩⟩, hsum, huniq⟩ :=
    AddSubgroup.isComplement_iff_existsUnique.mp (hA i) g
  let Hset : Set (G × ZMod N) := A ×ˢ ({0} : Set (ZMod N))
  let Kset : Set (G × ZMod N) := {x : G × ZMod N | ∃ i : Fin M, x.1 ∈ F i ∧ x.2 ∈ E i}
  let w : Hset × Kset :=
    ⟨⟨(a, (0 : ZMod N)), by
        change (a, (0 : ZMod N)) ∈ A ×ˢ ({0} : Set (ZMod N))
        exact Set.mem_prod.mpr ⟨haA, by simp⟩⟩,
     ⟨(f, z), by
        change (f, z) ∈ {x : G × ZMod N | ∃ i : Fin M, x.1 ∈ F i ∧ x.2 ∈ E i}
        exact ⟨i, hfF, hzi⟩⟩⟩
  refine ⟨w, ?_, ?_⟩
  · -- sum proof
    dsimp [w]
    simp [hsum]
  · intro y hy
    rcases y with ⟨y1, y2⟩
    rcases y1 with ⟨⟨a', z'⟩, hH'⟩
    rcases y2 with ⟨⟨f', z''⟩, hK'⟩
    have ha'A : a' ∈ A := (Set.mem_prod.mp hH').1
    have hz'0 : z' = 0 := by
      simpa using (Set.mem_prod.mp hH').2
    rcases hK' with ⟨j, hf'F, hz''E⟩
    have hfst : a' + f' = g := by
      exact congrArg Prod.fst hy
    have hsnd : z' + z'' = z := by
      exact congrArg Prod.snd hy
    have hz'' : z'' = z := by
      rw [hz'0, zero_add] at hsnd
      exact hsnd
    have hzEj : z ∈ E j := by
      exact hz'' ▸ hz''E
    have hji : j = i := by
      by_contra hji
      have hij : i ≠ j := by
        intro h
        exact hji h.symm
      have hd := hEdisj i j hij
      have hznot : z ∉ E j := (Set.disjoint_left.mp hd) hzi
      exact hznot hzEj
    have hf'Fi : f' ∈ F i := hji ▸ hf'F
    have hpair : ((⟨a', ha'A⟩ : A), (⟨f', hf'Fi⟩ : F i)) = ((⟨a, haA⟩ : A), (⟨f, hfF⟩ : F i)) := by
      exact huniq ((⟨a', ha'A⟩ : A), (⟨f', hf'Fi⟩ : F i)) hfst
    have ha' : a' = a := by
      exact congrArg Subtype.val (congrArg Prod.fst hpair)
    have hf' : f' = f := by
      exact congrArg Subtype.val (congrArg Prod.snd hpair)
    dsimp [w]
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact ha'
      · exact hz'0
    · apply Subtype.ext
      apply Prod.ext
      · exact hf'
      · exact hz''

end Commons.PeriodicTiling