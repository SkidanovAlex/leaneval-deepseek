import Mathlib
import Submission.Work.CORE2A.TorusDefs
import Submission.Work.L2F.Main

/-!
# CORE2A: `c14_k_two_n`

The centralizer in `L₂(q) ≤ PGL₂(q)` (`q = p ^ k`, `p` an odd prime, `q ≥ 5`) of an involution of
`L₂(q)` has order `q - 1` or `q + 1`.

`Work.GW2.Lsub p k = range (toPGL : PSL(2,GF(p,k)) →* PGL(2,GF(p,k)))`, so `Lsub p k` is a copy of
`L₂(q) = PSL(2,q)` inside `PGL₂(q)`.  Because `toPGL` is injective, the centralizer of
`y ∈ Lsub p k` inside `Lsub p k` is the image of the centralizer of the preimage `t ∈ PSL(2,q)` of
`y`, and the latter has cardinality `q - 1` or `q + 1` by the L2F area's
`Work.L2F.l2InvolutionCentralizer` (the centralizer of an involution of `L₂(q)` is dihedral of
order `q ∓ 1`).
-/

open scoped MatrixGroups

namespace Work.CORE2A

/-- **CORE2A `c14_k_two_n`.**  The centralizer in `L₂(q)` of an involution of `L₂(q)` has order
`q - 1` or `q + 1` (`q = p ^ k`, `p` odd, `q ≥ 5`). -/
theorem c14_k_two_n (T : Work.GW2.LocalToolkit) (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hk : 5 ≤ p ^ k)
    (y : Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)) (hy : y ∈ Work.GW2.Lsub p k) (hy2 : orderOf y = 2) :
    ∃ n : ℕ, (2 * n = p ^ k - 1 ∨ 2 * n = p ^ k + 1) ∧
      Nat.card ↥(Work.GW2.Lsub p k ⊓ Subgroup.centralizer ({y} : Set (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)))) = 2 * n := by
  classical
  -- `toPGL : PSL(2,q) →* PGL(2,q)` is injective with range `Lsub p k`.
  have hf : Function.Injective (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField p k)) :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  -- lift the involution `y` of `Lsub p k` to `t : PSL(2,q)`
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hy
  have ht2 : orderOf t = 2 := by
    rw [← orderOf_injective _ hf t, ht]; exact hy2
  -- the L2F area: the centralizer of an involution of `L₂(q)` is dihedral of order `q ∓ 1`
  obtain ⟨n, hn, hiso⟩ := Work.L2F.l2InvolutionCentralizer p k hp hk t ht2
  refine ⟨n, hn, ?_⟩
  -- the centralizer of `y` in `Lsub p k` is the `toPGL`-image of the centralizer of `t`
  have hcent : Subgroup.map (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField p k))
      (Subgroup.centralizer ({t} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))))
      = Work.GW2.Lsub p k ⊓ Subgroup.centralizer ({y} : Set (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k))) := by
    rw [← ht]
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      refine ⟨MonoidHom.mem_range.mpr ⟨s, rfl⟩, ?_⟩
      have h1 : Matrix.ProjectiveSpecialLinearGroup.toPGL s * Matrix.ProjectiveSpecialLinearGroup.toPGL t =
          Matrix.ProjectiveSpecialLinearGroup.toPGL t * Matrix.ProjectiveSpecialLinearGroup.toPGL s := by
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hs]
      exact Subgroup.mem_centralizer_singleton_iff.mpr h1
    · intro hx
      obtain ⟨hxL, hxc⟩ := hx
      obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hxL
      refine Subgroup.mem_map.mpr ⟨s, ?_, rfl⟩
      have h1 : s * t = t * s := by
        apply hf
        rw [map_mul, map_mul]
        exact (Subgroup.mem_centralizer_singleton_iff.mp hxc)
      exact Subgroup.mem_centralizer_singleton_iff.mpr h1
  -- `map` along an injective homomorphism preserves the cardinality
  rw [← hcent, Subgroup.card_map_of_injective hf]
  -- the dihedral isomorphism gives the cardinality `2 * n`
  obtain ⟨e⟩ := hiso
  rw [Nat.card_congr e.toEquiv]
  have hn0 : n ≠ 0 := by
    rcases hn with h | h <;> omega
  haveI : NeZero n := ⟨hn0⟩
  rw [Nat.card_eq_fintype_card, DihedralGroup.card]

end Work.CORE2A
