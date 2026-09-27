import Mathlib
import Submission.Work.Mostow.HLBasics

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow Work.Mostow

/-- An element of infinite order in a discrete subgroup of `PO n 1` acts without fixed points on
`ℍⁿ`. Indeed, if `γ • p = p` then all powers of `γ` displace the origin by at most `2 · hdist 0 p`,
so they lie in a finite set (`finite_nearStab`), while distinct powers are distinct because `γ` has
infinite order. -/
theorem no_fixed_of_orderOf_zero (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    (γ : Γ) (hγ : orderOf γ = 0) : ∀ p : E n, (γ : PO n 1) • p ≠ p := by
  intro p hp
  have hpb := POBasic.ofProp hA
  have hid := HypIsoData.ofProp hI
  have hinf : ¬ IsOfFinOrder γ := orderOf_eq_zero_iff.mp hγ
  -- every power of `γ` fixes `p`
  have hfixk : ∀ k : ℕ, ((γ ^ k : Γ) : PO n 1) • p = p := by
    intro k
    induction k with
    | zero => simpa using hpb.one_smul p
    | succ k ih =>
        rw [pow_succ, Subgroup.coe_mul, hpb.mul_smul, hp, ih]
  -- hence all powers displace the origin by at most `2 * hdist 0 p`
  have hmem : ∀ k : ℕ, (γ ^ k) ∈
      {γ' : Γ | hdist (0 : E n) ((γ' : PO n 1) • (0 : E n)) ≤ 2 * hdist (0 : E n) p} := by
    intro k
    have h1 := hid.triangle (0 : E n) p (((γ ^ k : Γ) : PO n 1) • (0 : E n))
    have h2 : hdist p (((γ ^ k : Γ) : PO n 1) • (0 : E n)) = hdist (0 : E n) p := by
      have h3 := hid.isom_smul (((γ ^ k : Γ) : PO n 1)) p (0 : E n)
      rw [hfixk k] at h3
      rw [h3, hid.symm]
    rw [h2] at h1
    simp only [Set.mem_ofPred_eq]
    linarith
  -- the near-stabiliser of the origin is finite
  have hfin := finite_nearStab hpb hid hdisc (2 * hdist (0 : E n) p)
  have hrange : (Set.range (fun k : ℕ => γ ^ k)).Finite :=
    hfin.subset (by rintro x ⟨k, rfl⟩; exact hmem k)
  exact Set.infinite_range_of_injective (injective_pow_iff_not_isOfFinOrder.mpr hinf) hrange

end Work.Mostow
