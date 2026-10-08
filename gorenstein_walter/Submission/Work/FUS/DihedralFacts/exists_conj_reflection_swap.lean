import Mathlib
import Submission.Work.FUS.Defs
import Submission.Work.Dihedral.Defs

namespace Work.FUS.DihedralFacts

/-- Let `n` be a positive multiple of `4`, `V ≤ DihedralGroup n` a four-group and `u ∈ V` a
non-identity element different from the central rotation `c = r (n/2)`. Then some rotation `s`
conjugates `u` to `u * c`.

Proof. If `u` were a rotation, then `u ^ 2 = 1` would force `u = 1` or `u = c` (the 2-torsion of
the cyclic group `⟨r⟩` is `{1, c}`), contrary to the hypotheses. So `u = sr i` is a reflection.
Conjugation by the rotation `r (n/4)` acts on reflections by `sr i ↦ sr (i - 2 * (n/4))`
(`Work.Dihedral.r_conj_sr`), while `sr i * r (n/2) = sr (i + n/2)`. Since `4 ∣ n` we have
`2 * (n/4) = n/2` and `-(n/2) = n/2` in `ZMod n`, so the two sides agree. -/
theorem exists_conj_reflection_swap (n : ℕ) [NeZero n] (h4 : 4 ∣ n) (V : Subgroup (DihedralGroup n))
    (hV : Work.GW2.IsFourGroup V) (u : DihedralGroup n) (hu : u ∈ V) (hu1 : u ≠ 1)
    (hu2 : u ≠ DihedralGroup.r ((n / 2 : ℕ) : ZMod n)) :
    ∃ s ∈ Work.Dihedral.rot n,
      s * u * s⁻¹ = u * DihedralGroup.r ((n / 2 : ℕ) : ZMod n) := by
  -- `u` is not a rotation: a rotation of order ≤ 2 in `DihedralGroup n` (`n` even) is `1` or
  -- the central rotation `r (n/2)`.
  have hnotrot : u ∉ Work.Dihedral.rot n := by
    intro hrot
    obtain ⟨i, rfl⟩ := Work.Dihedral.mem_rot.mp hrot
    have hsq : (DihedralGroup.r i : DihedralGroup n) ^ 2 = 1 := hV.2 _ hu
    have h2i : i = 0 ∨ i = ((n / 2 : ℕ) : ZMod n) := by
      have hsum : i + i = 0 := by
        have h : DihedralGroup.r (i + i) = DihedralGroup.r (0 : ZMod n) := by
          rw [← DihedralGroup.r_mul_r, ← pow_two, hsq, DihedralGroup.r_zero]
        exact DihedralGroup.r.inj h
      have hnegi : -i = i := (neg_eq_iff_add_eq_zero).mpr hsum
      rcases (ZMod.neg_eq_self_iff i).mp hnegi with h | h
      · exact Or.inl h
      · right
        have hval : i.val = n / 2 := by omega
        rw [← ZMod.natCast_zmod_val i, hval]
    rcases h2i with h | h
    · exact hu1 (by rw [h, DihedralGroup.r_zero])
    · exact hu2 (by rw [h])
  -- hence `u = sr i` is a reflection
  obtain ⟨i, hi⟩ := Work.Dihedral.notMem_rot.mp hnotrot
  subst hi
  refine ⟨DihedralGroup.r ((n / 4 : ℕ) : ZMod n), Work.Dihedral.r_mem_rot _, ?_⟩
  rw [Work.Dihedral.r_conj_sr, DihedralGroup.sr_mul_r]
  congr 1
  have hdiv : 2 * (n / 4) = n / 2 := by omega
  have hcast : (2 : ZMod n) * ((n / 4 : ℕ) : ZMod n) = ((n / 2 : ℕ) : ZMod n) := by
    have : ((2 * (n / 4) : ℕ) : ZMod n) = ((n / 2 : ℕ) : ZMod n) := by rw [hdiv]
    simpa using this
  have hhalf : ((n / 2 : ℕ) : ZMod n) + ((n / 2 : ℕ) : ZMod n) = 0 := by
    rw [← Nat.cast_add, show n / 2 + n / 2 = n by omega, ZMod.natCast_self]
  have hneg : -(((n / 2 : ℕ)) : ZMod n) = ((n / 2 : ℕ) : ZMod n) :=
    (neg_eq_iff_add_eq_zero).mpr hhalf
  rw [sub_eq_add_neg, hcast, hneg]

end Work.FUS.DihedralFacts
