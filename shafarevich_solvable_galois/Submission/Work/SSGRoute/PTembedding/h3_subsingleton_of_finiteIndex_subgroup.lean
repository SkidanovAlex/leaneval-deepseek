import Mathlib
import Submission.Work.AbsoluteKummer.All
import Submission.Work.SSGRoute.sha2_defs
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
import Submission.Work.SSGRoute.H3Map.mapC3c_mem_Z3_mem_B3
import Submission.Work.SSGRoute.PT.ClassFormation
import Submission.Work.SSGRoute.PTembedding.CoindTransfer
import Submission.Work.SSGRoute.PTembedding.coindTrace_equivariant
import Submission.Work.SSGRoute.PTembedding.h3_nsmul_prime_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H³(Γ,M) = 0` from `H³(S,M) = 0` for `S ≤ Γ` open of index prime to `p`

Let `Γ` be a compact group, `S ≤ Γ` an open subgroup of finite index with `p ∤ [Γ : S]`, and `M` a
finite `𝔽_p[Γ]`-module.  Then `H³(Γ,M)` injects into `H³(S,M)`; in particular the vanishing of
`H³(S,M)` forces that of `H³(Γ,M)`.

The injection is the classical composite

  `H³(Γ,M) --coindIncl_*--> H³(Γ, Coind_S^Γ M) --Shapiro≅--> H³(S,M)`,

whose injectivity is witnessed by the trace: the `Γ`-equivariant map
`coindTrace : Coind_S^Γ M → M` satisfies `coindTrace ∘ coindIncl = [Γ : S]` (`CoindTransfer.lean`),
so on `H³` it gives

  `mapH3 coindTrace ∘ coindIncl_* = [Γ : S] · id`,

and `[Γ : S]` is invertible on the `p`-torsion group `H³(Γ,M)` since `p ∤ [Γ : S]`.

The hypothesis `hshapiro` supplies the Shapiro isomorphism `H³(Γ, Coind_S^Γ M) ≅ H³(S,M)`.
-/

namespace Work.SSGRoute.PTembedding

/-- An element of an abelian group killed by `p` and by `n` is zero when `p` and `n` are
coprime (Bézout). -/
theorem eq_zero_of_nsmul_eq_zero_of_coprime {A : Type*} [AddCommGroup A] {p : ℕ} {x : A}
    (hpx : p • x = 0) {n : ℕ} (hn : n.Coprime p) (hnx : n • x = 0) : x = 0 := by
  have hbez := Nat.gcd_eq_gcd_ab n p
  have hgcd : (Nat.gcd n p : ℤ) = 1 := by rw [hn.gcd_eq_one]; rfl
  rw [hgcd] at hbez
  have hbez' : (Nat.gcdA n p : ℤ) * (n : ℤ) + (Nat.gcdB n p : ℤ) * (p : ℤ) = 1 := by
    rw [mul_comm (Nat.gcdA n p) (n : ℤ), mul_comm (Nat.gcdB n p) (p : ℤ)]
    exact hbez.symm
  have hx : x = (Nat.gcdA n p * (n : ℤ) + Nat.gcdB n p * (p : ℤ)) • x := by
    rw [hbez', one_smul]
  rw [hx, add_smul, mul_smul, mul_smul, natCast_zsmul, natCast_zsmul, hnx, hpx, smul_zero,
    smul_zero, add_zero]

theorem h3_subsingleton_of_finiteIndex_subgroup (p : ℕ) [Fact p.Prime] {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (S : Subgroup Γ)
    (hS : IsOpen (S : Set Γ)) [S.FiniteIndex] (hcop : Nat.Coprime S.index p)
    {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction Γ M]
    [SMulCommClass Γ (ZMod p) M] [Finite M]
    (hshapiro : Nonempty (Work.SSGRoute.H3 (M := Work.SSGRoute.PT.Coind Γ S M) Γ ≃+
      Work.SSGRoute.H3 (M := M) ↥S)) :
    Subsingleton (Work.SSGRoute.H3 (M := M) ↥S) →
      Subsingleton (Work.SSGRoute.H3 (M := M) Γ) := by
  intro hsub
  haveI hF : Fintype (Γ ⧸ S) := Subgroup.fintypeQuotientOfFiniteIndex
  obtain ⟨e⟩ := hshapiro
  -- Shapiro transports the vanishing from `S` to the coinduced module over `Γ`.
  have hsubC : Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.PT.Coind Γ S M) Γ) :=
    ⟨fun a b => e.injective (@Subsingleton.elim _ hsub (e a) (e b))⟩
  -- The unit `M → Coind_S^Γ M` and the trace `Coind_S^Γ M → M` are `Γ`-equivariant and compose
  -- to multiplication by `[Γ : S]`.
  have hΦ : Work.GroupCohomology.IsEquivariant Γ (coindIncl (M := M) S) :=
    coindIncl_equivariant S
  have hN : Work.GroupCohomology.IsEquivariant Γ (coindTrace (M := M) S) :=
    coindTrace_equivariant S
  -- Hence `H³(Γ,M) → H³(S,M) → H³(Γ,M)` is multiplication by `[Γ : S]`.
  have hkey : ∀ x : Work.SSGRoute.H3 (M := M) Γ, S.index • x = 0 := by
    intro x
    have h1 : (Work.SSGRoute.H3Map.mapH3 (coindTrace (M := M) S) hN)
        ((Work.SSGRoute.H3Map.mapH3 (coindIncl (M := M) S) hΦ) x) = S.index • x := by
      refine Work.SSGRoute.H3Map.H3_induction_on
        (C := fun y => (Work.SSGRoute.H3Map.mapH3 (coindTrace (M := M) S) hN)
          ((Work.SSGRoute.H3Map.mapH3 (coindIncl (M := M) S) hΦ) y) = S.index • y) x ?_
      intro c
      rw [Work.SSGRoute.H3Map.mapH3_H3π, Work.SSGRoute.H3Map.mapH3_H3π]
      have hc : Work.SSGRoute.H3Map.mapZ3 (coindTrace (M := M) S) hN
          (Work.SSGRoute.H3Map.mapZ3 (coindIncl (M := M) S) hΦ c) = S.index • c := by
        apply Subtype.ext
        funext q
        rw [Work.SSGRoute.H3Map.mapZ3_apply, Work.SSGRoute.H3Map.mapZ3_apply]
        exact coindTrace_coindIncl S ((c : Γ × Γ × Γ → M) q)
      rw [hc, map_nsmul]
    -- the left-hand side dies because `H³(Γ, Coind_S^Γ M)` is a subsingleton
    rw [← h1, hsubC.elim ((Work.SSGRoute.H3Map.mapH3 (coindIncl (M := M) S) hΦ) x) 0,
      map_zero]
  -- `H³(Γ,M)` is `p`-torsion, and `p` is coprime to `[Γ : S]`, so it vanishes.
  have hx0 : ∀ x : Work.SSGRoute.H3 (M := M) Γ, x = 0 := by
    intro x
    exact eq_zero_of_nsmul_eq_zero_of_coprime (h3_nsmul_prime_eq_zero p x) hcop (hkey x)
  exact ⟨fun x y => by rw [hx0 x, hx0 y]⟩

end Work.SSGRoute.PTembedding
