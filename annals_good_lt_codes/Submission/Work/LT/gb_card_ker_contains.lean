import Mathlib
import Submission.Work.LT.good_base_defs
import Submission.Work.LT.gb_card_bad_pair

/-!
# Counting the parity-check matrices whose code contains a fixed subspace

For a fixed subspace `U ≤ 𝔽₂^D` we count the parity-check matrices
`H : Fin r → Fin D → ZMod 2` whose kernel code `GB.kerCode H` contains `U`.

`U ≤ GB.kerCode H` means that every row `H k` of `H` annihilates `U`, i.e. lies in the
orthogonal complement `U^⊥ = GB.orth U = {h | ∀ w ∈ U, GB.dot h w = 0}`
(`GB.mem_orth`).  Hence the matrices in question are exactly the `r`-tuples of vectors of
`U^⊥`, i.e. the elements of `Fin r → GB.orth U`, and their number is `|U^⊥|^r`
(`Nat.card_fun`).

The orthogonal complement has cardinality `2^(D - frk U)`: the map `h ↦ (w ↦ dot h w)` is a
surjection `𝔽₂^D → U*` with kernel `U^⊥` — the dot pairing identifies `𝔽₂^D` with its dual
(`GB.dotEquiv`) and every linear functional on a subspace extends
(`LinearMap.dualMap_surjective_of_injective`) — so rank-nullity gives
`frk (U^⊥) = D - frk U` and `Module.natCard_eq_pow_finrank` gives `|U^⊥| = 2^(D - frk U)`
(`GB.card_orth`).

Hence `#{H | U ≤ kerCode H} = (2^(D - frk U))^r = 2^(r (D - frk U))`.
-/

set_option linter.unusedVariables false

namespace Work.LT

namespace GB

variable {D : ℕ}

/-- The parity-check matrices whose kernel code contains `U` are the `r`-tuples of vectors of
the orthogonal complement of `U`. -/
theorem card_kerCode_eq {D r : ℕ} (U : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    Nat.card {H : Fin r → Fin D → ZMod 2 // U ≤ kerCode H} = Nat.card (Fin r → orth U) := by
  refine Nat.card_congr
    { toFun := fun H k => ⟨H.1 k, ?_⟩
      invFun := fun g => ⟨fun k => (g k).1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- the `k`-th row of `H` annihilates `U`
    rw [mem_orth]
    intro w hw
    have hk : w ∈ kerCode H.1 := H.2 hw
    rw [mem_kerCode] at hk
    exact hk k
  · -- conversely an `r`-tuple of vectors of `U^⊥` has a kernel containing `U`
    intro w hw
    rw [mem_kerCode]
    intro k
    exact (mem_orth.mp (g k).2) w hw
  · intro H
    exact Subtype.ext rfl
  · intro g
    funext k
    exact Subtype.ext rfl

/-- Exact number of parity-check matrices `H : Fin r → Fin D → ZMod 2` whose kernel code
contains a fixed subspace `U`: it is `(2^(D - frk U))^r`. -/
theorem card_kerCode_contains {D r : ℕ} (U : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    Nat.card {H : Fin r → Fin D → ZMod 2 // U ≤ kerCode H} = 2 ^ (r * (D - frk U)) := by
  have horth : Nat.card (orth U) = 2 ^ (D - frk U) := by
    simpa only [frk] using card_orth U
  rw [card_kerCode_eq, Nat.card_fun, Nat.card_fin, horth, ← pow_mul, mul_comm]

end GB

/-- Exact count of the parity-check matrices `H : Fin r → Fin D → ZMod 2` whose kernel code contains a fixed subspace `U`: these are the `r`-tuples of vectors of the annihilator `U^⊥ = {h | ∀ w ∈ U, dot h w = 0}`, of cardinality `2^(D - frk U)` (rank-nullity for the surjection `h ↦ (w ↦ dot h w)` from `(Fin D → ZMod 2)` onto `Module.Dual (ZMod 2) U`; surjectivity: linear functionals on a subspace extend, `LinearMap.dualMap_surjective_of_injective`, and the dot product identifies the space with its dual; `Module.natCard_eq_pow_finrank`, `Submodule.finrank_quotient`). -/
theorem gb_card_ker_contains {D r : ℕ} (U : Submodule (ZMod 2) (Fin D → ZMod 2)) :
    (Nat.card {H : Fin r → Fin D → ZMod 2 // U ≤ GB.kerCode H} : ℝ) =
      (2 : ℝ) ^ ((r : ℝ) * (D - GB.frk U)) := by
  rw [GB.card_kerCode_contains]
  have hle : GB.frk U ≤ D := by
    have h := Submodule.finrank_le U
    rw [Module.finrank_fintype_fun_eq_card] at h
    simpa [GB.frk] using h
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_sub hle]

end Work.LT
