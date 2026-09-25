import Mathlib

namespace NK.LocalCFT.Units.EllRank

/-- If `V ≤ W` are additive subgroups of an abelian group `G` with `[W : V] = p` a prime,
then `W/V` is cyclic of order `p`: there is `w ∈ W \ V` such that every `x ∈ W` differs
from an integral multiple of `w` by an element of `V`.

Indeed, for any `w ∈ W \ V` the subgroup `T = V ⊔ ℤw` satisfies
`V.relIndex T * T.relIndex W = p`; since `w ∉ V` the first factor is not `1`, hence equals
`p`, forcing `T.relIndex W = 1`, i.e. `T = W`. -/
theorem exists_sub_mem_of_relIndex_prime {G : Type*} [AddCommGroup G] {V W : AddSubgroup G} (hVW : V ≤ W)
    {p : ℕ} (hp : p.Prime) (h : V.relIndex W = p) :
    ∃ w : G, w ∈ W ∧ w ∉ V ∧ ∀ x ∈ W, ∃ m : ℤ, x - m • w ∈ V := by
  have hne : V ≠ W := by
    intro hVW'
    rw [hVW', AddSubgroup.relIndex_self] at h
    exact hp.ne_one h.symm
  obtain ⟨w, hwW, hwV⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hVW hne)
  refine ⟨w, hwW, hwV, ?_⟩
  set T : AddSubgroup G := V ⊔ AddSubgroup.closure {w} with hT
  have hVT : V ≤ T := le_sup_left
  have hcw : AddSubgroup.closure ({w} : Set G) ≤ W :=
    (AddSubgroup.closure_le W).mpr (by simpa using hwW)
  have hTW : T ≤ W := sup_le hVW hcw
  have hmul : V.relIndex T * T.relIndex W = p :=
    (AddSubgroup.relIndex_mul_relIndex V T W hVT hTW).trans h
  have hd : V.relIndex T = p := by
    rcases (Nat.dvd_prime hp).mp ⟨T.relIndex W, hmul.symm⟩ with h1 | hp'
    · exfalso
      have hTV : T ≤ V := AddSubgroup.relIndex_eq_one.mp h1
      have hwT : w ∈ T := by
        rw [hT]
        exact AddSubgroup.mem_sup.mpr ⟨0, V.zero_mem, w, AddSubgroup.subset_closure rfl, by simp⟩
      exact hwV (hTV hwT)
    · exact hp'
  have hidx : T.relIndex W = 1 := by
    have h2 : p * T.relIndex W = p := by simpa [hd] using hmul
    exact Nat.mul_left_cancel hp.pos (by simpa using h2)
  have hWT : W ≤ T := AddSubgroup.relIndex_eq_one.mp hidx
  intro x hxW
  have hxT : x ∈ T := hWT hxW
  rw [hT, AddSubgroup.mem_sup] at hxT
  obtain ⟨v, hv, y, hy, hsum⟩ := hxT
  rw [AddSubgroup.mem_closure_singleton] at hy
  obtain ⟨m, hm⟩ := hy
  exact ⟨m, by rw [← hsum, ← hm]; simpa using hv⟩

end NK.LocalCFT.Units.EllRank
