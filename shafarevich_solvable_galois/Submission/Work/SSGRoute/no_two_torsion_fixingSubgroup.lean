import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Submission.Work.SSGRoute.TwoTorsion.add_mem_normSet
import Submission.Work.SSGRoute.TwoTorsion.neg_one_notMem_normSet
import Submission.Work.SSGRoute.TwoTorsion.rootOfUnity_eq_pm_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `G_ℚ` has no involution fixing a field that contains a non-trivial root of unity

`K ⊆ ℚ̄` with `μ_{p^{i+1}} ⊆ K` and `i ≥ 1` (so `p^{i+1} ≥ 4`): then no element of order two of
`G_ℚ = Gal(ℚ̄/ℚ)` fixes `K` pointwise.  Equivalently, `Gal(ℚ̄/K)` is torsion free at `2`.

The proof is the Artin–Schreier style argument, carried out in `TwoTorsion/`: if `c` were a
non-trivial involution fixing `K` then `c` is a ring involution of the algebraically closed field
`ℚ̄`, and the norm set `normSet c = {x * c x | x ≠ 0}` of the quadratic extension `ℚ̄ / ℚ̄^c`
yields a positivity cone on the fixed field `ℚ̄^c`:

* `-1` is not a norm (`neg_one_notMem_normSet`);
* the norm set is closed under addition (`add_mem_normSet`), so together with `0` it is an
  ordering of `ℚ̄^c`;
* consequently every root of unity fixed by `c` is `±1` (`rootOfUnity_eq_pm_one`).

But `c` fixes a primitive `p^{i+1}`-st root of unity `ζ` with `p^{i+1} ≥ 4`, which is neither `1`
nor `-1`.
-/

namespace Work.SSGRoute

open TwoTorsion

theorem no_two_torsion_fixingSubgroup (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) (i : ℕ) (hi : 1 ≤ i)
    (hμ : SSGRoute.HasRootsOfUnity p K i) :
    ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup → c = 1 := by
  intro c hc2 hcK
  by_contra hc1
  obtain ⟨ζ, hζK, hζ⟩ := hμ
  -- `c` fixes `ζ`
  have hfix : c ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff K c).mp hcK ζ hζK
  -- `c` viewed as a ring involution of `ℚ̄`
  have hcc : (c * c : SSGRoute.GalQ) = 1 := by rw [← pow_two, hc2]
  have hcring : c.toRingEquiv * c.toRingEquiv = 1 := by
    ext x
    have h : (c * c) x = (1 : SSGRoute.GalQ) x := by rw [hcc]
    simpa using h
  have hcring1 : c.toRingEquiv ≠ 1 := by
    intro h
    refine hc1 (AlgEquiv.ext fun x => ?_)
    have := congrArg (fun f : SSGRoute.QBar ≃+* SSGRoute.QBar => f x) h
    simpa using this
  -- the norm set of `c` misses `-1` and is closed under addition
  have hneg : (-1 : SSGRoute.QBar) ∉ TwoTorsion.normSet c.toRingEquiv :=
    TwoTorsion.neg_one_notMem_normSet (Ω := SSGRoute.QBar) c.toRingEquiv hcring hcring1
  have hadd : ∀ w ∈ TwoTorsion.normSet c.toRingEquiv,
      ∀ w' ∈ TwoTorsion.normSet c.toRingEquiv,
        w + w' ∈ TwoTorsion.normSet c.toRingEquiv :=
    fun w hw w' hw' =>
      TwoTorsion.add_mem_normSet (Ω := SSGRoute.QBar) c.toRingEquiv hcring hneg hw hw'
  -- the exponent is at least `4`
  have hn1 : 1 ≤ p ^ (i + 1) := Nat.one_le_pow (i + 1) p (Fact.out : p.Prime).pos
  have hgt : 2 < p ^ (i + 1) := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have h1 : 2 ^ 2 ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (i + 1) ≤ p ^ (i + 1) := Nat.pow_le_pow_left hp2 (i + 1)
    omega
  -- a root of unity fixed by `c` is `±1`
  have hres : ζ = 1 ∨ ζ = -1 :=
    TwoTorsion.rootOfUnity_eq_pm_one (Ω := SSGRoute.QBar) c.toRingEquiv hneg hadd hn1 hfix
      hζ.pow_eq_one
  rcases hres with h | h
  · exact hζ.ne_one (by omega) h
  · rw [h] at hζ
    have hord : p ^ (i + 1) = orderOf (-1 : SSGRoute.QBar) := hζ.eq_orderOf
    rw [orderOf_neg_one, ringChar.eq_zero] at hord
    norm_num at hord
    omega

end Work.SSGRoute
