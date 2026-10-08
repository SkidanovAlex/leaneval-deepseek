import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Dihedral.centralizer_sr_subset
import Submission.Work.L2F.Dihedral.fourGroup_two_nonidentity
import Submission.Work.L2F.Dihedral.fourGroup_contains_reflection

namespace Work.L2F.Dihedral

open DihedralGroup

/-- A subgroup all of whose elements are involutions is abelian, hence contained in its own
centralizer. -/
lemma le_centralizer_of_sq_eq_one {G : Type*} [Group G] {V : Subgroup G}
    (hsq : ∀ v ∈ V, v ^ 2 = 1) : V ≤ Subgroup.centralizer (V : Set G) := by
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hv2 : v * v = 1 := by simpa [pow_two] using hsq v hv
  have hw2 : w * w = 1 := by simpa [pow_two] using hsq w hw
  have h1 : (v * w) * (v * w) = 1 := by simpa [pow_two] using hsq (v * w) (V.mul_mem hv hw)
  have h3 : w * v = (v * w)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hv2, inv_eq_of_mul_eq_one_right hw2]
  rw [h3, inv_eq_of_mul_eq_one_left h1]

/-- A four-subgroup of a dihedral group is self-centralizing.  Proof: let `V ≤ DihedralGroup m`
with `|V| = 4`.  Every element of `V` is an involution (that is `IsFourGroup`), and a non-rotation
element `sr i` has order `2`, or `sr i * sr j = r (j - i)`, so any two commuting reflections `sr i`,
`sr j` satisfy `r (j-i) = r (i-j)`, i.e. `2(j-i) = 0`; hence every `V` is
`{1, r (m/2), sr i, sr (i + m/2)}` for a reflection `sr i` (`m` must be even), and the centralizer of
a reflection `sr i` is `{1, r (m/2), sr i, sr (i + m/2)}` (an element of `⟨r⟩` centralizing `sr i`
satisfies `2k = 0`, a reflection `sr j` centralizing `sr i` satisfies `2(j - i) = 0`).  Hence
`C(V) = V`.  (For odd `m` no subgroup of order `4` exists, so the statement is vacuous.) -/
theorem fourGroup_centralizer_dihedral {m : ℕ} (V : Subgroup (DihedralGroup m))
    (hV : Work.L2F.IsFourGroup V) :
    Subgroup.centralizer (V : Set (DihedralGroup m)) = V := by
  obtain ⟨hcard, hsq⟩ := hV
  -- `V` is abelian, so it lies in its own centralizer.
  have hVle : V ≤ Subgroup.centralizer (V : Set (DihedralGroup m)) :=
    le_centralizer_of_sq_eq_one hsq
  -- Structure of `V`: it contains a reflection `sr i` and the rotation `r (m/2)`.
  obtain ⟨i, hsi, hhalf⟩ := fourGroup_contains_reflection V hcard hsq
  -- Hence every element of the four-element set `S` below lies in `V`.
  have hSV : ({1, r ((m / 2 : ℕ) : ZMod m), sr i,
      sr (i + ((m / 2 : ℕ) : ZMod m))} : Set (DihedralGroup m)) ⊆ V := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact V.one_mem
    · exact hhalf
    · exact hsi
    · rw [← sr_mul_r i ((m / 2 : ℕ) : ZMod m)]
      exact V.mul_mem hsi hhalf
  -- The whole centralizer of `V` is contained in the centralizer of `sr i`, which is `S`.
  have hCV : Subgroup.centralizer (V : Set (DihedralGroup m)) ≤
      Subgroup.centralizer ({sr i} : Set (DihedralGroup m)) :=
    Subgroup.centralizer_le (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hsi)
  exact le_antisymm (fun x hx => hSV (centralizer_sr_subset (hCV hx))) hVle

end Work.L2F.Dihedral
