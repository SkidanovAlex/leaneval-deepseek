import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.typeB
import Submission.Work.Higman.layers_card_dichotomy_alt

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/- Auxiliary declarations for `Work.Higman.typeB_of_odd_fpf`, kept in a private namespace so
that they cannot collide with the many other files in `Submission/Work/Higman`. -/
namespace TBofOddFpf

/-- Every automorphism of a group preserves its centre (self-contained copy). -/
theorem mulAut_mem_center {G : Type} [Group G] (φ : MulAut G) {z : G}
    (hz : z ∈ Subgroup.center G) : φ z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  calc g * φ z = φ (φ.symm g * z) := by rw [map_mul, MulEquiv.apply_symm_apply]
    _ = φ (z * φ.symm g) := by rw [hz (φ.symm g)]
    _ = φ z * g := by rw [map_mul, MulEquiv.apply_symm_apply]

/-- An automorphism `w` commuting with `ξ` carries a `ξ`-invariant layer to a `ξ`-invariant
layer: it preserves the centre (as does every automorphism), it preserves `ξ`-invariance, and
it preserves the order. -/
theorem map_mulAut {ξ w : MulAut P} (hcomm : w * ξ = ξ * w)
    {M : Subgroup P} (hM : IsXiLayer ξ M) : IsXiLayer ξ (M.map w.toMonoidHom) := by
  obtain ⟨hZ, hξ, hcard⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [Subgroup.mem_map]
    exact ⟨w⁻¹ z, hZ (mulAut_mem_center w⁻¹ hz), by simp⟩
  · intro x hx
    rw [Subgroup.mem_map] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨ξ y, hξ y hy, by
      have h := congrArg (fun f : MulAut P => f y) hcomm
      simpa [MulAut.mul_apply] using h⟩
  · rw [Subgroup.card_map_of_injective (MulEquiv.injective w), hcard]

/-- The self-map induced by an automorphism `w` commuting with `ξ` on the type of
`ξ`-invariant layers. -/
def layerMap (ξ w : MulAut P) (hcomm : w * ξ = ξ * w) :
    {M : Subgroup P // IsXiLayer ξ M} → {M : Subgroup P // IsXiLayer ξ M} :=
  fun M => ⟨M.1.map w.toMonoidHom, map_mulAut hcomm M.2⟩

end TBofOddFpf

/-- **D3 (the consumers' criterion, Peterfalvi II Ch. V §2 Lemma 6).**  An automorphism `w` of
odd order `≠ 1` commuting with `ξ` and moving every `ξ`-invariant layer forces type `B`
(a `2`-element set admits no fixed-point-free permutation of odd order, so D1's first case is
excluded). -/
theorem typeB_of_odd_fpf {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {ξ w : MulAut P} (hξ : Work.Higman.FpfXi ξ)
    (hcomm : w * ξ = ξ * w) (hodd : Odd (orderOf w)) (hw1 : w ≠ 1)
    (hfree : ∀ M : Subgroup P, Work.Higman.IsXiLayer ξ M → M.map w.toMonoidHom ≠ M) :
    Work.Higman.IsTypeB ξ := by
  classical
  rcases layers_card_dichotomy_alt h hξ with h2 | hq
  · -- the number of layers is `2`: `w` acts on it as an odd-order permutation without fixed
    -- points, which is impossible.
    exfalso
    have hcomm_inv : (w⁻¹ : MulAut P) * ξ = ξ * w⁻¹ := by
      have hc : Commute w ξ := hcomm
      exact hc.inv_left.eq
    have hleft : Function.LeftInverse (TBofOddFpf.layerMap ξ w⁻¹ hcomm_inv) (TBofOddFpf.layerMap ξ w hcomm) := by
      intro M
      apply Subtype.ext
      show (M.1.map w.toMonoidHom).map (w⁻¹).toMonoidHom = M.1
      rw [Subgroup.map_map]
      have hcomp : ((w⁻¹ : MulAut P).toMonoidHom.comp w.toMonoidHom) = MonoidHom.id P := by
        ext x
        simp
      rw [hcomp, Subgroup.map_id]
    have hright : Function.RightInverse (TBofOddFpf.layerMap ξ w⁻¹ hcomm_inv) (TBofOddFpf.layerMap ξ w hcomm) := by
      intro M
      apply Subtype.ext
      show (M.1.map (w⁻¹).toMonoidHom).map w.toMonoidHom = M.1
      rw [Subgroup.map_map]
      have hcomp : (w.toMonoidHom.comp (w⁻¹ : MulAut P).toMonoidHom) = MonoidHom.id P := by
        ext x
        simp
      rw [hcomp, Subgroup.map_id]
    let σ : Equiv.Perm {M : Subgroup P // IsXiLayer ξ M} :=
      { toFun := TBofOddFpf.layerMap ξ w hcomm
        invFun := TBofOddFpf.layerMap ξ w⁻¹ hcomm_inv
        left_inv := hleft
        right_inv := hright }
    have hσval : ∀ M : {M : Subgroup P // IsXiLayer ξ M},
        (σ M).1 = M.1.map w.toMonoidHom := fun M => rfl
    -- `σ ^ k` maps a layer to the layer induced by `w ^ k`
    have hσpow : ∀ (k : ℕ) (M : {M : Subgroup P // IsXiLayer ξ M}),
        ((σ ^ k) M).1 = M.1.map ((w ^ k).toMonoidHom) := by
      intro k
      induction k with
      | zero =>
          intro M
          rw [pow_zero, pow_zero, Equiv.Perm.one_apply]
          exact (Subgroup.map_id M.1).symm
      | succ k ih =>
          intro M
          have hstep : (σ ^ (k + 1)) M = σ ((σ ^ k) M) := by
            rw [pow_succ']
            rfl
          rw [hstep, hσval ((σ ^ k) M), ih M]
          rw [Subgroup.map_map]
          congr 1
          ext x
          simp [pow_succ', MulAut.mul_apply]
    have hσr : σ ^ orderOf w = 1 := by
      apply Equiv.ext
      intro M
      have h1 : (σ ^ orderOf w) M = M := by
        apply Subtype.ext
        rw [hσpow (orderOf w) M, pow_orderOf_eq_one]
        exact Subgroup.map_id M.1
      simpa using h1
    -- `σ` has no fixed point, and `L` has two elements, so `σ` is an involution
    have hfix : ∀ M : {M : Subgroup P // IsXiLayer ξ M}, σ M ≠ M := by
      intro M hcon
      have hval : M.1.map w.toMonoidHom = M.1 := by
        have := congrArg (Subtype.val) hcon
        simpa [hσval M] using this
      exact hfree M.1 M.2 hval
    have hσ2 : σ ^ 2 = 1 := by
      apply Equiv.ext
      intro M
      have hpair : ({M, σ M} : Set {M : Subgroup P // IsXiLayer ξ M}).ncard = 2 :=
        Set.ncard_pair (fun h => hfix M h.symm)
      have huniv : (Set.univ : Set {M : Subgroup P // IsXiLayer ξ M}) = {M, σ M} := by
        have h1 : ({M, σ M} : Set {M : Subgroup P // IsXiLayer ξ M}) = Set.univ := by
          apply Set.eq_of_subset_of_ncard_le (by intro x _; trivial)
          rw [Set.ncard_univ, hpair, h2]
        exact h1.symm
      have hmem : σ (σ M) ∈ ({M, σ M} : Set {M : Subgroup P // IsXiLayer ξ M}) := by
        rw [← huniv]
        trivial
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rw [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      rcases hmem with h | h
      · exact h
      · exact absurd (σ.injective h) (hfix M)
    have hdiv : orderOf σ = 1 := by
      have h1 : orderOf σ ∣ orderOf w := orderOf_dvd_iff_pow_eq_one.mpr hσr
      have h2' : orderOf σ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hσ2
      have hg : orderOf σ ∣ Nat.gcd (orderOf w) 2 := Nat.dvd_gcd h1 h2'
      have hcop : Nat.gcd (orderOf w) 2 = 1 := (Nat.coprime_two_right.mpr hodd).gcd_eq_one
      exact Nat.dvd_one.mp (by rwa [hcop] at hg)
    have hσone : σ = 1 := orderOf_eq_one_iff.mp hdiv
    obtain ⟨M0⟩ : Nonempty {M : Subgroup P // IsXiLayer ξ M} :=
      (Nat.card_pos_iff.mp (by omega)).1
    have hval : M0.1.map w.toMonoidHom = M0.1 := by
      have h1 : σ M0 = M0 := by rw [hσone]; rfl
      have := congrArg (Subtype.val) h1
      simpa [hσval M0] using this
    exact hfree M0.1 M0.2 hval
  · rw [IsTypeB, hq]

end Work.Higman
