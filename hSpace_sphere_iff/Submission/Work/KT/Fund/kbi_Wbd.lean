import Mathlib
import Submission.Work.KT.Fund.kbi_defs

/-!
# `Work.KT.Fund.kbi_Wbd`

The two disc-images `W1p`, `W2p` of the target idempotent of `kappa_bott` (see
`Work.KT.Fund.KBI`) agree on the boundary circle `X × S¹`.  This is the gluing datum which makes
`W` a well defined projection over `X × S²` (the "clutching" of the two disc data).

Concretely `W1p = Pd ⊗ₖ h1m + Qd ⊗ₖ E00` and `W2p = Pd ⊗ₖ h2m + Qd ⊗ₖ E00`, so it suffices that
the two rank-one projections

* `h1m = c • [[1, ζ̄], [ζ, |ζ|²]]` (projection onto the line spanned by `(1, ζ)`) and
* `h2m = c • [[|ζ|², ζ̄], [ζ, 1]]` (projection onto the line spanned by `(ζ̄, 1)`)

coincide on the circle `|ζ| = 1`, where the normalising factor `c = (1 + |ζ|²)⁻¹` becomes `1/2`,
the coordinate `ζ` becomes the tautological unit `z` of `C(X × S¹, ℂ)` and `ζ̄` becomes `z⁻¹`
(compare `Work.KT.Fund.KBI.bdryRestrict_zc`, `bdryRestrict_zcb`, `bdryRestrict_zcn`).

Note: `rw`/`simp` cannot use the `h1m_apply_*` lemmas directly, because a rewrite pattern which
applies a *matrix* to indices is not type correct at the transparency level used by the matcher
(`Matrix` is a semireducible type synonym).  The entry computations below are therefore phrased in
terms of `h1m`/`h2m` themselves (unfolded with `split_ifs`) and in terms of lemmas whose patterns
never apply a matrix to an index, such as `Work.KT.Fund.bdry_map_add` and
`Work.KT.Fund.bdry_map_kron`.
-/

namespace Work.KT.Fund

open _root_.Matrix
open scoped Kronecker

namespace KBI

/-- The tautological unit `z` of `C(X × S¹, ℂ)` multiplied with its inverse is `1`. -/
lemma zUnit_coe_mul_coe_inv (X : Type) [TopologicalSpace X] :
    (zUnit X : C(X × Sph ℂ, ℂ)) * (↑((zUnit X)⁻¹) : C(X × Sph ℂ, ℂ)) = 1 :=
  Units.mul_inv (zUnit X)

/-- Both chart projections restrict to `(1/2) • [[1, z⁻¹], [z, 1]]` on the equator: there
`|ζ|² = 1`, `c = 1/2`, `ζ` is the unit `z` and `ζ̄` is `z⁻¹`, so `ζ · ζ̄ = 1`. -/
lemma bdry_h1m_h2m (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (p q : Fin 2) :
    bdryRestrict X (h1m X p q) = bdryRestrict X (h2m X p q) := by
  simp only [h1m, h2m, _root_.Matrix.of_apply]
  split_ifs with hp hq
  all_goals
    simp only [map_mul, bdryRestrict_zcn, bdryRestrict_zc, bdryRestrict_zcb,
      zUnit_coe_mul_coe_inv, mul_one]

end KBI

/-- `bdryRestrict` commutes with the entrywise sum of matrices. -/
lemma bdry_map_add (X : Type) [TopologicalSpace X] {m n : Type*}
    (A B : Matrix m n (KBI.kdD X)) :
    (A + B).map (fun f => bdryRestrict X f) =
      A.map (fun f => bdryRestrict X f) + B.map (fun f => bdryRestrict X f) :=
  Matrix.map_add (fun f => bdryRestrict X f) (fun a b => map_add (bdryRestrict X) a b) A B

/-- `bdryRestrict` commutes with the Kronecker product of matrices. -/
lemma bdry_map_kron (X : Type) [TopologicalSpace X] {l m n p : Type*}
    (A : Matrix l m (KBI.kdD X)) (B : Matrix n p (KBI.kdD X)) :
    (A ⊗ₖ B).map (fun f => bdryRestrict X f) =
      (A.map (fun f => bdryRestrict X f)) ⊗ₖ (B.map (fun f => bdryRestrict X f)) := by
  funext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  show bdryRestrict X (A i₁ j₁ * B i₂ j₂) =
    bdryRestrict X (A i₁ j₁) * bdryRestrict X (B i₂ j₂)
  exact map_mul (bdryRestrict X) (A i₁ j₁) (B i₂ j₂)

theorem kbi_Wbd (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n : ℕ) (P : Matrix (Fin n) (Fin n) C(X, ℂ)) :
    (Work.KT.Fund.KBI.W1p X n P).map (fun f => Work.KT.Fund.bdryRestrict X f) =
      (Work.KT.Fund.KBI.W2p X n P).map (fun f => Work.KT.Fund.bdryRestrict X f) := by
  have hmap : (Work.KT.Fund.KBI.h1m X).map (fun f => Work.KT.Fund.bdryRestrict X f) =
      (Work.KT.Fund.KBI.h2m X).map (fun f => Work.KT.Fund.bdryRestrict X f) := by
    funext p q
    show Work.KT.Fund.bdryRestrict X (Work.KT.Fund.KBI.h1m X p q) =
      Work.KT.Fund.bdryRestrict X (Work.KT.Fund.KBI.h2m X p q)
    exact Work.KT.Fund.KBI.bdry_h1m_h2m X p q
  simp only [Work.KT.Fund.KBI.W1p, Work.KT.Fund.KBI.W2p, bdry_map_add, bdry_map_kron, hmap]

end Work.KT.Fund
