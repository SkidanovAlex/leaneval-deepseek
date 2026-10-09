import Mathlib
import Submission.Work.SSGRoute.prop5.magnus_mem_one_add
import Submission.Work.SSGRoute.prop5.magnusGroupPart
import Submission.Work.SSGRoute.prop5.core.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Magnus leading term at the sharp truncation

This file collects the facts about the Magnus leading term `magLead N z = magnus X N z - 1`
needed for the proof of the Magnus core theorem, at the truncation level `N = k + 1` adapted to
elements of `γ_k` (Mathlib: `Gam X (k-1)`):

* `monBrk_coeff_length`, `monBrk_mem_fil`: homogeneity of the bracketed monomial `monBrk`;
* `magLead_monGrp_sub_mem`: the leading term of a commutator monomial is the bracketed monomial;
* `magLead_mul_mem`, `magLead_zpow`, `magLead_prod`: additivity of the leading term on `γ_k`;
* `magLead_eq_zero_of_mem`: reduction of the truncation level.

The proofs of the last four are adapted from `prop5/magnusGroupPart.lean` (where the same facts are
proved with the less sharp hypothesis `N ≤ 2*k`).
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5
namespace core

variable {X : Type*}

/-! ## Homogeneity of the bracketed monomial -/

/-- `monBrk X c` is a combination of words of length exactly `Magma.size c`. -/
theorem monBrk_coeff_length (c : Magma X) (v : FreeMonoid X) (h : (monBrk X c).coeff v ≠ 0) :
    v.length = Magma.size c := by
  classical
  have hmain : ∀ (c : Magma X) (v : FreeMonoid X), v ∈ (monBrk X c).coeff.support →
      v.length = Magma.size c := by
    intro c
    induction c with
    | gen x =>
        intro v hv
        rw [monBrk_gen, MonoidAlgebra.coeff_single] at hv
        have hv' : v = FreeMonoid.of x := by
          by_contra hne
          rw [Finsupp.mem_support_iff] at hv
          exact hv (Finsupp.single_eq_of_ne hne)
        rw [hv']
        simp
    | mul a b iha ihb =>
        intro v hv
        rw [monBrk_mul, MonoidAlgebra.coeff_sub] at hv
        rcases Finset.mem_union.mp (Finsupp.support_sub hv) with hv | hv
        · rcases Finset.mem_mul.mp
            (MonoidAlgebra.support_coeff_mul_subset (monBrk X a) (monBrk X b) hv) with
            ⟨u, hu, u', hu', rfl⟩
          rw [FreeMonoid.length_mul, iha u hu, ihb u' hu', Magma.size_mul]
        · rcases Finset.mem_mul.mp
            (MonoidAlgebra.support_coeff_mul_subset (monBrk X b) (monBrk X a) hv) with
            ⟨u, hu, u', hu', rfl⟩
          rw [FreeMonoid.length_mul, ihb u hu, iha u' hu', Magma.size_mul, Nat.add_comm]
  exact hmain c v (by rwa [Finsupp.mem_support_iff])

/-- `monBrk X c` lies in the `size c`-th filtration ideal. -/
theorem monBrk_mem_fil (c : Magma X) : monBrk X c ∈ fil X (Magma.size c) := by
  rw [fil_eq_filI]
  change monBrk X c ∈ filz X (Magma.size c)
  rw [mem_filz_iff]
  intro w hw
  exact le_of_eq (monBrk_coeff_length c w hw).symm

/-- The image of `monBrk X c` in `FreeAssoc X ⧸ fil X N` lies in `filq X N (size c)`. -/
theorem monBrk_mk_mem_filq (N : ℕ) (c : Magma X) :
    Ideal.Quotient.mk (fil X N) (monBrk X c) ∈ filq X N (Magma.size c) :=
  Ideal.mem_map_of_mem (Ideal.Quotient.mk (fil X N)) (monBrk_mem_fil c)

@[simp] theorem monBrk_gen_eq_wordEl (x : X) : monBrk X (Magma.gen x) = wordEl [x] := by
  rw [monBrk_gen, wordEl]
  congr 1

/-- Membership in a filtration piece transported across an equality of the exponents. -/
theorem mem_filq_of_eq {N a b : ℕ} (h : a = b) {x : FreeAssoc X ⧸ fil X N}
    (hx : x ∈ filq X N a) : x ∈ filq X N b := h ▸ hx

/-! ## The leading term of a commutator monomial -/

/-- **The Magnus leading term of a commutator monomial is the bracketed monomial.** -/
theorem magLead_monGrp_sub_mem (N : ℕ) (c : Magma X) (hN : Magma.size c + 1 ≤ N) :
    magLead N (monGrp X c) - Ideal.Quotient.mk (fil X N) (monBrk X c) ∈
      filq X N (Magma.size c + 1) := by
  induction c with
  | gen x =>
      have h1 : magLead N (monGrp X (Magma.gen x)) =
          Ideal.Quotient.mk (fil X N) (monBrk X (Magma.gen x)) := by
        rw [monGrp_gen, magLead_of, monBrk_gen_eq_wordEl]
      rw [h1, sub_self]
      exact Submodule.zero_mem _
  | mul a b iha ihb =>
      have hpa : 1 ≤ Magma.size a := Magma.size_pos a
      have hpb : 1 ≤ Magma.size b := Magma.size_pos b
      have hsum : Magma.size a + Magma.size b + 1 ≤ N := by
        rw [Magma.size_mul] at hN; omega
      have hia : Magma.size a + 1 ≤ N := by omega
      have hib : Magma.size b + 1 ≤ N := by omega
      have hIa := iha hia
      have hIb := ihb hib
      have hcomm := magLead_commutator N (Magma.size a) (Magma.size b) hpa hpb hsum
        (core.monGrp_mem_Gam (X := X) a) (core.monGrp_mem_Gam (X := X) b)
      have hAa : magLead N (monGrp X a) ∈ filq X N (Magma.size a) :=
        magLead_mem_filq N (Magma.size a) hpa (by omega) (core.monGrp_mem_Gam (X := X) a)
      have hBb : magLead N (monGrp X b) ∈ filq X N (Magma.size b) :=
        magLead_mem_filq N (Magma.size b) hpb (by omega) (core.monGrp_mem_Gam (X := X) b)
      have hMa : Ideal.Quotient.mk (fil X N) (monBrk X a) ∈ filq X N (Magma.size a) :=
        monBrk_mk_mem_filq N a
      have hMb : Ideal.Quotient.mk (fil X N) (monBrk X b) ∈ filq X N (Magma.size b) :=
        monBrk_mk_mem_filq N b
      -- the difference of the two brackets lies in the next piece
      have hdiff : magLead N ⁅monGrp X a, monGrp X b⁆
          - (Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
             - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a))
          ∈ filq X N (Magma.size a + Magma.size b + 1) := by
        have hAB : magLead N (monGrp X a) * magLead N (monGrp X b)
            - Ideal.Quotient.mk (fil X N) (monBrk X a)
              * Ideal.Quotient.mk (fil X N) (monBrk X b) ∈ filq X N (Magma.size a + Magma.size b + 1) := by
          have he : magLead N (monGrp X a) * magLead N (monGrp X b)
              - Ideal.Quotient.mk (fil X N) (monBrk X a)
                * Ideal.Quotient.mk (fil X N) (monBrk X b)
              = (magLead N (monGrp X a) - Ideal.Quotient.mk (fil X N) (monBrk X a))
                  * magLead N (monGrp X b)
                + Ideal.Quotient.mk (fil X N) (monBrk X a)
                  * (magLead N (monGrp X b) - Ideal.Quotient.mk (fil X N) (monBrk X b)) := by
            noncomm_ring
          rw [he]
          refine Submodule.add_mem _ ?_ ?_
          · have := mul_mem_filq X N (Magma.size a + 1) (Magma.size b) hIa hBb
            exact mem_filq_of_eq (by omega) this
          · have := mul_mem_filq X N (Magma.size a) (Magma.size b + 1) hMa hIb
            exact mem_filq_of_eq (by omega) this
        have hBA : magLead N (monGrp X b) * magLead N (monGrp X a)
            - Ideal.Quotient.mk (fil X N) (monBrk X b)
              * Ideal.Quotient.mk (fil X N) (monBrk X a) ∈ filq X N (Magma.size a + Magma.size b + 1) := by
          have he : magLead N (monGrp X b) * magLead N (monGrp X a)
              - Ideal.Quotient.mk (fil X N) (monBrk X b)
                * Ideal.Quotient.mk (fil X N) (monBrk X a)
              = (magLead N (monGrp X b) - Ideal.Quotient.mk (fil X N) (monBrk X b))
                  * magLead N (monGrp X a)
                + Ideal.Quotient.mk (fil X N) (monBrk X b)
                  * (magLead N (monGrp X a) - Ideal.Quotient.mk (fil X N) (monBrk X a)) := by
            noncomm_ring
          rw [he]
          refine Submodule.add_mem _ ?_ ?_
          · have := mul_mem_filq X N (Magma.size b + 1) (Magma.size a) hIb hAa
            exact mem_filq_of_eq (by omega) this
          · have := mul_mem_filq X N (Magma.size b) (Magma.size a + 1) hMb hIa
            exact mem_filq_of_eq (by omega) this
        have hsub : (magLead N (monGrp X a) * magLead N (monGrp X b)
              - magLead N (monGrp X b) * magLead N (monGrp X a))
            - (Ideal.Quotient.mk (fil X N) (monBrk X a)
                * Ideal.Quotient.mk (fil X N) (monBrk X b)
              - Ideal.Quotient.mk (fil X N) (monBrk X b)
                * Ideal.Quotient.mk (fil X N) (monBrk X a))
            ∈ filq X N (Magma.size a + Magma.size b + 1) := by
          have he : (magLead N (monGrp X a) * magLead N (monGrp X b)
              - magLead N (monGrp X b) * magLead N (monGrp X a))
            - (Ideal.Quotient.mk (fil X N) (monBrk X a)
                * Ideal.Quotient.mk (fil X N) (monBrk X b)
              - Ideal.Quotient.mk (fil X N) (monBrk X b)
                * Ideal.Quotient.mk (fil X N) (monBrk X a))
            = (magLead N (monGrp X a) * magLead N (monGrp X b)
                - Ideal.Quotient.mk (fil X N) (monBrk X a)
                  * Ideal.Quotient.mk (fil X N) (monBrk X b))
              - (magLead N (monGrp X b) * magLead N (monGrp X a)
                - Ideal.Quotient.mk (fil X N) (monBrk X b)
                  * Ideal.Quotient.mk (fil X N) (monBrk X a)) := by
            noncomm_ring
          rw [he]
          exact Submodule.sub_mem _ hAB hBA
        have hsum := Submodule.add_mem _ hcomm hsub
        have he : (magLead N ⁅monGrp X a, monGrp X b⁆
              - (magLead N (monGrp X a) * magLead N (monGrp X b)
                 - magLead N (monGrp X b) * magLead N (monGrp X a)))
            + ((magLead N (monGrp X a) * magLead N (monGrp X b)
                 - magLead N (monGrp X b) * magLead N (monGrp X a))
              - (Ideal.Quotient.mk (fil X N) (monBrk X a)
                  * Ideal.Quotient.mk (fil X N) (monBrk X b)
                - Ideal.Quotient.mk (fil X N) (monBrk X b)
                  * Ideal.Quotient.mk (fil X N) (monBrk X a)))
            = magLead N ⁅monGrp X a, monGrp X b⁆
              - (Ideal.Quotient.mk (fil X N) (monBrk X a)
                  * Ideal.Quotient.mk (fil X N) (monBrk X b)
                - Ideal.Quotient.mk (fil X N) (monBrk X b)
                  * Ideal.Quotient.mk (fil X N) (monBrk X a)) := by
          noncomm_ring
        rw [he] at hsum
        exact hsum
      -- conclude
      rw [monGrp_mul]
      simpa only [Magma.size_mul, monBrk_mul, map_sub, map_mul] using hdiff

/-! ## Additivity at the sharp truncation -/

theorem magLead_mul_mem (k : ℕ) (hk : 1 ≤ k) {y z : FreeGroup X}
    (hy : y ∈ Gam X (k - 1)) (hz : z ∈ Gam X (k - 1)) :
    magLead (k + 1) (y * z) = magLead (k + 1) y + magLead (k + 1) z :=
  magLead_mul (k + 1) k hk (by omega) (by omega) hy hz

theorem magLead_inv_mem (k : ℕ) (hk : 1 ≤ k) {y : FreeGroup X} (hy : y ∈ Gam X (k - 1)) :
    magLead (k + 1) y⁻¹ = -magLead (k + 1) y :=
  magLead_inv (k + 1) k hk (by omega) (by omega) hy

theorem magLead_pow_mem (k : ℕ) (hk : 1 ≤ k) (p : ℕ) {y : FreeGroup X}
    (hy : y ∈ Gam X (k - 1)) :
    magLead (k + 1) (y ^ p) = (p : ℤ) • magLead (k + 1) y := by
  rw [magLead_pow (k + 1) k p hk (by omega) (by omega) hy, zsmul_eq_mul]

/-- **The Magnus leading term converts integer powers into scalar multiples.** -/
theorem magLead_zpow (k : ℕ) (hk : 1 ≤ k) (m : ℤ) {y : FreeGroup X}
    (hy : y ∈ Gam X (k - 1)) :
    magLead (k + 1) (y ^ m) = m • magLead (k + 1) y := by
  rcases Int.eq_nat_or_neg m with ⟨n, h | h⟩
  · rw [h, zpow_natCast, magLead_pow_mem k hk n hy]
  · rw [h, show y ^ (-(n : ℤ)) = (y ^ n)⁻¹ by rw [zpow_neg, zpow_natCast]]
    rw [magLead_inv_mem k hk (Subgroup.pow_mem _ hy n), magLead_pow_mem k hk n hy, neg_smul]

/-! ## Reduction of the truncation level -/

/-- If the Magnus leading term modulo `fil N` lies in the degree `n+2` part, then it vanishes
modulo `fil (n+2)`. -/
theorem magLead_eq_zero_of_mem (N n : ℕ) (hn : n + 2 ≤ N) (y : FreeGroup X)
    (h : magLead N y ∈ filq X N (n + 2)) : magLead (n + 2) y = 0 := by
  have hle : fil X N ≤ fil X (n + 2) := fil_antitone X hn
  let π : FreeAssoc X ⧸ fil X N →+* FreeAssoc X ⧸ fil X (n + 2) := Ideal.Quotient.factor hle
  have hπmk : ∀ a : FreeAssoc X,
      π (Ideal.Quotient.mk (fil X N) a) = Ideal.Quotient.mk (fil X (n + 2)) a :=
    fun a => Ideal.Quotient.factor_mk hle a
  have hnat : (Units.map π.toMonoidHom).comp (magnus X N) = magnus X (n + 2) := by
    refine FreeGroup.ext_hom _ _ (fun x => ?_)
    apply Units.ext
    simp only [MonoidHom.comp_apply, Units.coe_map]
    rw [magnus_of X N x, magnus_of X (n + 2) x]
    change π (1 + Ideal.Quotient.mk (fil X N) (MonoidAlgebra.single (FreeMonoid.of x) 1)) =
      1 + Ideal.Quotient.mk (fil X (n + 2)) (MonoidAlgebra.single (FreeMonoid.of x) 1)
    rw [map_add, map_one, hπmk]
  have hval : π (↑((magnus X N) y)) = ↑((magnus X (n + 2)) y) := by
    have h2 := congrArg (fun u : (FreeAssoc X ⧸ fil X (n + 2))ˣ =>
      (u : FreeAssoc X ⧸ fil X (n + 2))) (DFunLike.congr_fun hnat y)
    rw [MonoidHom.comp_apply, Units.coe_map] at h2
    exact h2
  have h1 : π (magLead N y) = magLead (n + 2) y := by
    show π (↑((magnus X N) y) - 1) = _
    rw [map_sub, map_one, hval]
    rfl
  obtain ⟨a, ha, haeq⟩ := (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (fil X N))
    Ideal.Quotient.mk_surjective).1 h
  rw [← h1, ← haeq, hπmk]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr ha

end core
end Work.SSGRoute.prop5
