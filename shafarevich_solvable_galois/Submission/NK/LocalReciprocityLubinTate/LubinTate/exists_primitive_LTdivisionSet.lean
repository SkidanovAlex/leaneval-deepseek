import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.DivisionPoints
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Integers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocityLubinTate.LubinTate

/-- **Primitive division points exist at every level `n ≥ 1`.**  The `π^n`-division points `Λ_n`
of the standard Lubin–Tate group strictly contain the `π^{n-1}`-division points `Λ_{n-1}` (Milne,
*CFT*, §I.3): since `Λ_n` is nested in `Λ_{n+1}` and `Λ_n` has `q^n` elements with `q = #𝓀[F] ≥ 2`,
the inclusion `Λ_{n-1} ⊆ Λ_n` cannot be an equality for `n ≥ 1`.

Consequently there is a *primitive* `π^n`-division point, i.e. a point of `Λ_n \ Λ_{n-1}`, whose
minimal polynomial over `F` is the Eisenstein factor `f^{[n-1]}`. -/
theorem exists_primitive_LTdivisionSet {F : Type*} [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : ↥(ValuativeRel.valuation F).integer) (hπ : Irreducible π) (n : ℕ) (hn : 1 ≤ n) :
    ∃ y : AlgebraicClosure F,
      y ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
          (NK.LocalReciprocityLubinTate.residueCard F) n ∧
      y ∉ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
          (NK.LocalReciprocityLubinTate.residueCard F) (n - 1) := by
  by_contra h
  push Not at h
  have hq : 2 ≤ NK.LocalReciprocityLubinTate.residueCard F :=
    NK.LocalReciprocityLubinTate.two_le_residueCard F
  -- If no point of `Λ_n` were new, then `Λ_n ⊆ Λ_{n-1}`; with the reverse inclusion this forces
  -- the two sets to be equal.
  have hsub :
      NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
          (NK.LocalReciprocityLubinTate.residueCard F) n ⊆
        NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
          (NK.LocalReciprocityLubinTate.residueCard F) (n - 1) :=
    fun y hy => h y hy
  have hmono :
      NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
          (NK.LocalReciprocityLubinTate.residueCard F) (n - 1) ⊆
        NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F)
          (NK.LocalReciprocityLubinTate.residueCard F) n :=
    NK.LocalReciprocityLubinTate.LTdivisionSet_mono F (π : F)
      (NK.LocalReciprocityLubinTate.residueCard F) hq (Nat.sub_le n 1)
  have heq := le_antisymm hsub hmono
  -- Comparing cardinalities gives `q^n = q^(n-1)`, which is impossible for `q ≥ 2`, `n ≥ 1`.
  have h1 := NK.LocalReciprocityLubinTate.ncard_LTdivisionSet F π hπ
    (NK.LocalReciprocityLubinTate.residueCard F) n hq
  have h2 := NK.LocalReciprocityLubinTate.ncard_LTdivisionSet F π hπ
    (NK.LocalReciprocityLubinTate.residueCard F) (n - 1) hq
  rw [heq] at h1
  have hpow : NK.LocalReciprocityLubinTate.residueCard F ^ (n - 1) <
      NK.LocalReciprocityLubinTate.residueCard F ^ n :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

end NK.LocalReciprocityLubinTate.LubinTate
