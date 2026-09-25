import Mathlib
import Submission.Work.ConCohomology.All

namespace Work.ShafarevichKoch

open Work.ConCohomology

/-- **The invariants `H¹(N,M)^G` detected on commutators.**

For an extension `1 → N → G → Q → 1` (`GroupExt G Q N`), a discrete `N`-module `M = ZMod 2`
whose `N`-action is trivial (it is the restriction of a *trivial* `G`-action along `i`, via
`hcompN` and `htrivG`), and a `1`-cocycle `z : Z¹(N,ZMod 2)`:

`z` is fixed by the conjugation action of `G` on `H¹(N,ZMod 2)` if and only if `z` vanishes on all
commutators `E.conj g n * n⁻¹ = i⁻¹(g · i n · g⁻¹ · (i n)⁻¹)` of the extension.

Since the action on `ZMod 2` is trivial, `B¹(N,ZMod 2) = 0`, so the invariants condition is simply
`conjCochain g z = z`, i.e. `z (E.conj g⁻¹ n) = z n` for all `g, n`; and since `z` is then additive,
`z (E.conj g n * n⁻¹) = z (E.conj g n) - z n`. Both conditions therefore say exactly that `z` is
invariant under conjugation. -/
theorem mem_H1Invariants_iff_commutator
    {G Q N : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
    [DistribMulAction G (ZMod 2)] [DistribMulAction N (ZMod 2)]
    [Work.ConCohomology.IsDiscreteGModule N (ZMod 2)]
    (E : Work.ConCohomology.GroupExt G Q N)
    (hcont : ∀ g : G, Continuous (E.conj g))
    (hcompN : ∀ (n : N) (m : ZMod 2), n • m = E.i n • m)
    (htrivG : ∀ (g : G) (m : ZMod 2), g • m = m)
    (z : Work.ConCohomology.Z1 N (ZMod 2)) :
    Work.ConCohomology.H1.mk z ∈ Work.ConCohomology.H1Invariants E hcont hcompN ↔
      ∀ (g : G) (n : N),
        (z : Work.ConCohomology.Cochain1 N (ZMod 2)) (E.conj g n * n⁻¹) = 0 := by
  -- The `N`-action on `ZMod 2` is the restriction of the (trivial) `G`-action along `E.i`.
  have htrivN : ∀ (n : N) (m : ZMod 2), n • m = m := fun n m => by
    rw [hcompN n m, htrivG (E.i n) m]
  -- `z` is therefore an additive map `N → ZMod 2`.
  have hcoc : IsCocycle1 ((z : Cochain1 N (ZMod 2)) : N → ZMod 2) := mem_Z1.mp z.2
  have hadd : ∀ x y : N, (z : Cochain1 N (ZMod 2)) (x * y) =
      (z : Cochain1 N (ZMod 2)) x + (z : Cochain1 N (ZMod 2)) y :=
    (isCocycle1_iff_of_trivial htrivN _).mp hcoc
  have hzero : (z : Cochain1 N (ZMod 2)) 1 = 0 := isCocycle1_apply_one hcoc
  have hinv : ∀ n : N, (z : Cochain1 N (ZMod 2)) n⁻¹ = - (z : Cochain1 N (ZMod 2)) n := by
    intro n
    have h := hadd n⁻¹ n
    rw [inv_mul_cancel, hzero] at h
    exact add_eq_zero_iff_eq_neg.mp h.symm
  -- `z` vanishes on `E.conj g n * n⁻¹` exactly when `z` is conjugation invariant.
  have hkey : ∀ (g : G) (n : N),
      (z : Cochain1 N (ZMod 2)) (E.conj g n * n⁻¹) = 0 ↔
      (z : Cochain1 N (ZMod 2)) (E.conj g n) = (z : Cochain1 N (ZMod 2)) n := by
    intro g n
    rw [hadd (E.conj g n) n⁻¹, hinv n, add_eq_zero_iff_eq_neg]
    constructor
    · intro h; simpa using h
    · intro h; simpa using h
  -- The trivial action makes `B¹(N,ZMod 2)` vanish, so the invariants are a plain fixed-point set.
  have hB1 : B1' N (ZMod 2) = ⊥ := B1'_eq_bot htrivN
  rw [mem_H1Invariants]
  constructor
  · intro hmem g n
    have hg : conjH1Map E hcont hcompN g (H1.mk z) = H1.mk z := hmem g
    rw [conjH1Map_mk] at hg
    have hcz : conjZ1Map E hcont hcompN g z = z := by
      have hsub := (H1.mk_eq_mk_iff (conjZ1Map E hcont hcompN g z) z).mp hg
      rw [hB1] at hsub
      exact sub_eq_zero.mp (AddSubgroup.mem_bot.mp hsub)
    have hcf : conjCochain E hcont g (z : Cochain1 N (ZMod 2)) =
        (z : Cochain1 N (ZMod 2)) := by
      have := congrArg (fun w : Z1 N (ZMod 2) => (w : Cochain1 N (ZMod 2))) hcz
      simpa using this
    have hconj : E.conj g⁻¹ (E.conj g n) = n := by
      rw [← GroupExt.conj_mul, inv_mul_cancel, GroupExt.conj_one]
    have h1 : conjCochain E hcont g (z : Cochain1 N (ZMod 2)) (E.conj g n) =
        (z : Cochain1 N (ZMod 2)) (E.conj g n) := by rw [hcf]
    rw [conjCochain_apply, hconj, htrivG g] at h1
    exact (hkey g n).mpr h1.symm
  · intro h g
    rw [conjH1Map_mk, H1.mk_eq_mk_iff, hB1, AddSubgroup.mem_bot, sub_eq_zero]
    apply Subtype.ext
    ext n
    change conjCochain E hcont g (z : Cochain1 N (ZMod 2)) n = (z : Cochain1 N (ZMod 2)) n
    rw [conjCochain_apply, htrivG g]
    exact (hkey g⁻¹ n).mp (h g⁻¹ n)

end Work.ShafarevichKoch
