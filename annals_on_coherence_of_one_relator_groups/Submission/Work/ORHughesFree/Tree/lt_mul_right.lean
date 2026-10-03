import Mathlib
import Submission.Work.ORHughesFree.Tree.order_defs
import Submission.Work.ORHughesFree.Tree.fam_mul
import Submission.Work.ORHughesFree.Tree.edge
import Submission.Work.ORHughesFree.Tree.mulMs_basic
import Submission.Work.ORHughesFree.Tree.lt_add_right
import Submission.Work.ORHughesFree.Tree.fam_basic

/-!
# Strict order is invariant under multiplying by a non-zero tree on the right

The well-order `lt` on finite rooted trees
(`Submission/Work/ORHughesFree/Tree/order_defs.lean`) is the Dershowitz–Manna ordering of the
families of children.  Multiplication acts on families by the multiset product
`mulMs M N = {a + b | a ∈ M, b ∈ N}` (`Tree.mulMs`), i.e. `fam (x * y) = mulMs (fam x) (fam y)`.

Since the Dershowitz–Manna ordering is compatible with the monoid operation `+`
(`Tree.lt_add_right`), it is compatible with the multiset product by a nonempty multiset.  This
is the content of the lemma below, transferred from families to trees through `fam_mul`.
-/

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- **Multiplying by a nonempty multiset on the right preserves the Dershowitz–Manna
ordering.**  If `M` is below `N` and `K ≠ 0`, then `mulMs M K` is below `mulMs N K`: the
witnessing decomposition `N = X + Z` over `M = X + Y` is multiplied by `K`, and each element of
`Y` dominated by an element of `Z` is shifted by the same element of `K`, using
`Tree.lt_add_right`. -/
theorem dmLT_mulMs_right {M N K : Multiset Tree} (h : dmLT lt M N) (hK : K ≠ 0) :
    dmLT lt (mulMs M K) (mulMs N K) := by
  obtain ⟨X, Y, Z, hZ, hM, hN, hYZ⟩ := h
  refine ⟨mulMs X K, mulMs Y K, mulMs Z K, ?_, ?_, ?_, ?_⟩
  · exact mulMs_ne_zero.mpr ⟨hZ, hK⟩
  · rw [hM, mulMs_add_left]
  · rw [hN, mulMs_add_left]
  · intro u hu
    rw [mem_mulMs] at hu
    obtain ⟨y, hy, k, hk, rfl⟩ := hu
    obtain ⟨z, hz, hyz⟩ := hYZ y hy
    exact ⟨z + k, mem_mulMs.mpr ⟨z, hz, k, hk, rfl⟩, lt_add_right hyz k⟩

/-- **Multiplying by a non-zero tree on the right preserves the strict order**: if `a < b` and
`c ≠ 0` then `a * c < b * c`. -/
theorem lt_mul_right {a b c : Tree} (h : lt a b) (hc : c ≠ 0) : lt (a * c) (b * c) := by
  have hK : fam c ≠ 0 := ne_zero_iff_fam_ne_zero.mp hc
  rw [lt_iff_dmLT] at h ⊢
  rw [show fam (a * c) = mulMs (fam a) (fam c) from fam_mul a c,
    show fam (b * c) = mulMs (fam b) (fam c) from fam_mul b c]
  exact dmLT_mulMs_right h hK

end Work.ORHughesFree.Tree
