import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.clChi_conj
import Submission.Work.ORLyndon.CLDirect.clChi_eq_one_of_mem

namespace Work.ORLyndon.CLDirect

/-- The value of the character `clChi` on the `k`-th power of `u`: `clChi (u^k) = ofAdd (k : ZMod l)`.

Since `clChi` is a monoid homomorphism, it suffices to know `clChi u = ofAdd 1`, which is
`clChi_conj` with `f = 1` (the Cohen--Lyndon basis element attached to the identity coset is a
conjugate of `u`, and `1 * u * 1⁻¹ = u`); the power is then `ofAdd_nsmul` and `nsmul_eq_mul`. -/
theorem clChi_pow_ofAdd {X : Type*} {u : FreeGroup X} (D : Work.ORLyndon.CLDirect.CLData u)
    (l k : ℕ) (h : u ^ k ∈ Subgroup.normalClosure ({u} : Set (FreeGroup X))) :
    Work.ORLyndon.CLDirect.clChi D l ⟨u ^ k, h⟩ = Multiplicative.ofAdd (k : ZMod l) := by
  have hmem : u ∈ Subgroup.normalClosure ({u} : Set (FreeGroup X)) :=
    Subgroup.subset_normalClosure (Set.mem_singleton u)
  have hsub : (⟨u ^ k, h⟩ : ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) =
      (⟨u, hmem⟩ : ↥(Subgroup.normalClosure ({u} : Set (FreeGroup X)))) ^ k := by
    ext
    simp
  have h1 : Work.ORLyndon.CLDirect.clChi D l ⟨u, hmem⟩ =
      Multiplicative.ofAdd (1 : ZMod l) := by
    have hf : (1 : FreeGroup X) * u * 1⁻¹ ∈
        Subgroup.normalClosure ({u} : Set (FreeGroup X)) := by
      simpa using hmem
    simpa using Work.ORLyndon.CLDirect.clChi_conj D l 1 hf
  rw [hsub, map_pow, h1, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]

/-- KMS/FKS order statement, char-free, axiom-clean. Sketch: `orderOf_eq_iff (by omega)`; `w^l = 1` by `← map_pow`, `presentRho_relator`; for `0 < k < l`, if `w^k = 1` then `u^k ∈ normalClosure {u^l}` (`← map_pow`, `PresentedGroup.mk_eq_one_iff`; `presentRho_apply` is `rfl`), so `clChi_eq_one_of_mem` gives `clChi (u^k) = 1`, while `clChi (u^k) = clChi(u)^k = ofAdd (k : ZMod l)` by `clChi_conj` with `f = 1` (rewrite `1 * u * 1⁻¹ = u`); thus `(k : ZMod l) = 0`, i.e. `l ∣ k` by `ZMod.natCast_zmod_eq_zero_iff_dvd`, contradicting `0 < k < l`. -/
theorem orderOf_presentRho_of_clData {X : Type*} {u : FreeGroup X}
    (D : Work.ORLyndon.CLDirect.CLData u) (l : ℕ) (hl : 1 ≤ l) :
    orderOf (Work.ORLyndon.presentRho (u ^ l) u) = l := by
  classical
  -- It suffices to have `w ^ l = 1` and no smaller positive exponent killing `w`.
  rw [orderOf_eq_iff (by omega)]
  refine ⟨?_, ?_⟩
  · -- `w ^ l = presentRho (u^l) (u^l) = 1` since `u^l` is the relator.
    rw [← map_pow, Work.ORLyndon.presentRho_relator]
  · intro k hkl hk0 hpow
    -- `w ^ k = 1` means `u ^ k ∈ ⟪u^l⟫ = N`.
    have hpow' : Work.ORLyndon.presentRho (u ^ l) (u ^ k) = 1 := by
      rw [← map_pow] at hpow
      exact hpow
    have hmem : u ^ k ∈ Subgroup.normalClosure ({u ^ l} : Set (FreeGroup X)) :=
      PresentedGroup.mk_eq_one_iff.mp hpow'
    -- On the one hand `clChi` kills all of `N = ⟪u^l⟫`.
    have hchi1 : Work.ORLyndon.CLDirect.clChi D l ⟨u ^ k, normalClosure_pow_le u l hmem⟩ = 1 :=
      Work.ORLyndon.CLDirect.clChi_eq_one_of_mem D l (u ^ k) hmem
    -- On the other hand `clChi (u^k) = ofAdd (k : ZMod l)`.
    have hchi2 : Work.ORLyndon.CLDirect.clChi D l ⟨u ^ k, normalClosure_pow_le u l hmem⟩ =
        Multiplicative.ofAdd (k : ZMod l) :=
      Work.ORLyndon.CLDirect.clChi_pow_ofAdd D l k (normalClosure_pow_le u l hmem)
    -- Hence `(k : ZMod l) = 0`, i.e. `l ∣ k`.
    have hzero : (k : ZMod l) = 0 := by
      have h : Multiplicative.ofAdd (k : ZMod l) = 1 := by rw [← hchi2, hchi1]
      exact congrArg Multiplicative.toAdd h
    have hdvd : l ∣ k := (ZMod.natCast_eq_zero_iff k l).mp hzero
    -- contradicting `0 < k < l`.
    have := Nat.le_of_dvd hk0 hdvd
    omega

end Work.ORLyndon.CLDirect
