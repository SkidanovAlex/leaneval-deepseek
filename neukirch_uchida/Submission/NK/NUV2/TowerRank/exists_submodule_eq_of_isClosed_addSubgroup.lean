import Mathlib

/-!
# Closed additive subgroups of `ℤ_[ℓ]^r` are `ℤ_[ℓ]`-submodules

Let `ℓ` be a prime and let `H ≤ (ℤ_[ℓ])^r` be an **additive** subgroup which is closed in the
`ℓ`-adic topology.  Then `H` is automatically stable under the action of the whole ring `ℤ_[ℓ]`:
for `x ∈ H` the set `{b : ℤ_[ℓ] | b • x ∈ H}` is closed (it is the preimage of the closed set `H`
under the continuous map `b ↦ b • x`) and contains the dense subring `ℤ ⊆ ℤ_[ℓ]`
(`PadicInt.denseRange_intCast`), hence it is all of `ℤ_[ℓ]`.

Consequently `H` carries the structure of a `ℤ_[ℓ]`-submodule with the same underlying set, which
is the content of `NK.NUV2.TowerRank.exists_submodule_eq_of_isClosed_addSubgroup`.
-/

namespace NK.NUV2.TowerRank

/-- A closed additive subgroup of `(ℤ_[ℓ])^r` is stable under `ℤ_[ℓ]`-scalar multiplication,
because `ℤ ⊆ ℤ_[ℓ]` is dense and scalar multiplication is continuous. -/
theorem smul_mem_of_isClosed_addSubgroup {ℓ r : ℕ} [Fact ℓ.Prime]
    (H : AddSubgroup (Fin r → PadicInt ℓ)) (hH : IsClosed (H : Set (Fin r → PadicInt ℓ)))
    (a : PadicInt ℓ) (x : Fin r → PadicInt ℓ) (hx : x ∈ H) : a • x ∈ H := by
  -- the set of scalars preserving `H` at `x` is closed …
  have hclosed : IsClosed {b : PadicInt ℓ | b • x ∈ H} :=
    hH.preimage (continuous_id.smul continuous_const)
  -- … and contains the dense subring `ℤ`.
  have hmem : ∀ k : ℤ, (k : PadicInt ℓ) • x ∈ H := by
    intro k
    rw [Int.cast_smul_eq_zsmul]
    exact H.zsmul_mem hx k
  exact PadicInt.denseRange_intCast.induction_on a hclosed hmem

theorem exists_submodule_eq_of_isClosed_addSubgroup {ℓ r : ℕ} [Fact ℓ.Prime]
    (H : AddSubgroup (Fin r → PadicInt ℓ)) (hH : IsClosed (H : Set (Fin r → PadicInt ℓ))) :
    ∃ H' : Submodule (PadicInt ℓ) (Fin r → PadicInt ℓ),
      (H' : Set (Fin r → PadicInt ℓ)) = (H : Set (Fin r → PadicInt ℓ)) := by
  refine ⟨{ carrier := (H : Set (Fin r → PadicInt ℓ)),
            zero_mem' := H.zero_mem,
            add_mem' := fun {a b : Fin r → PadicInt ℓ} (ha : a ∈ (H : Set _)) (hb : b ∈ (H : Set _)) =>
              H.add_mem ha hb,
            smul_mem' := fun (c : PadicInt ℓ) {x : Fin r → PadicInt ℓ} (hx : x ∈ (H : Set _)) =>
              smul_mem_of_isClosed_addSubgroup H hH c x hx }, rfl⟩

end NK.NUV2.TowerRank
