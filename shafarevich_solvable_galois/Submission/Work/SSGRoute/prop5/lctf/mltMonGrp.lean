import Mathlib
import Submission.Work.SSGRoute.prop5.lctf.coreDefs
import Submission.Work.SSGRoute.prop5.witt.Vocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Magnus leading term of a tree commutator monomial

For a binary tree `c` of size `k` the group commutator monomial `monGrp X c` and the bracketed
monomial `monBrk X c` are matched by the Magnus leading term `mlt`:

`mlt N (monGrp X c) ≡ monBrk X c`  modulo the `(k+1)`-st filtration piece of `FreeAssoc X ⧸ fil X N`

whenever `k + 1 ≤ N`.  Proved by induction on the tree using the bracket lemma `mlt_commutator`.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5.lctf

open Work.SSGRoute.prop5

/-- The bracketed monomial attached to a tree of size `k` lies in the `k`-th filtration ideal. -/
theorem monBrk_mem_fil (X : Type*) (c : Magma X) :
    monBrk X c ∈ fil X (Magma.size c) := by
  induction c with
  | gen x =>
      rw [monBrk_gen, Magma.size_gen]
      exact Ideal.subset_span ⟨FreeMonoid.of x, by simp, rfl⟩
  | mul a b iha ihb =>
      rw [monBrk_mul, Magma.size_mul]
      refine Submodule.sub_mem _ ?_ ?_
      · exact fil_mul_le X (Magma.size a) (Magma.size b) (Ideal.mul_mem_mul iha ihb)
      · exact fil_antitone X (by omega)
          (fil_mul_le X (Magma.size b) (Magma.size a) (Ideal.mul_mem_mul ihb iha))

/-- The leading term of the group commutator monomial of a tree `c` agrees with the bracketed
monomial `monBrk X c` modulo `filq X N (size c + 1)`. -/
theorem mlt_monGrp_sub_mem_aux (X : Type) :
    ∀ (c : Magma X) (N : ℕ), Magma.size c + 1 ≤ N →
      mlt N (monGrp X c) - Ideal.Quotient.mk (fil X N) (monBrk X c) ∈
        filq X N (Magma.size c + 1) := by
  intro c
  induction c with
  | gen x =>
      intro N hN
      rw [monGrp_gen, Magma.size_gen, monBrk_gen, mlt_of]
      rw [sub_self]
      exact Submodule.zero_mem _
  | mul a b iha ihb =>
      intro N hN
      have hpaq : Magma.size a + Magma.size b + 1 ≤ N := by simpa [Magma.size_mul] using hN
      have hp : 1 ≤ Magma.size a := Magma.size_pos a
      have hq : 1 ≤ Magma.size b := Magma.size_pos b
      have hpa : Magma.size a + 1 ≤ N := by omega
      have hqb : Magma.size b + 1 ≤ N := by omega
      have ha := iha N hpa
      have hb := ihb N hqb
      have hLTa : mlt N (monGrp X a) ∈ filq X N (Magma.size a) :=
        mlt_mem_filq N (Magma.size a) hp (by omega) (monGrp_mem_Gam a)
      have hLTb : mlt N (monGrp X b) ∈ filq X N (Magma.size b) :=
        mlt_mem_filq N (Magma.size b) hq (by omega) (monGrp_mem_Gam b)
      have hBa : Ideal.Quotient.mk (fil X N) (monBrk X a) ∈ filq X N (Magma.size a) :=
        Ideal.mem_map_of_mem _ (monBrk_mem_fil X a)
      have hBb : Ideal.Quotient.mk (fil X N) (monBrk X b) ∈ filq X N (Magma.size b) :=
        Ideal.mem_map_of_mem _ (monBrk_mem_fil X b)
      have hcomm := mlt_commutator N (Magma.size a) (Magma.size b) hp hq hpaq
        (u := monGrp X a) (v := monGrp X b)
        (monGrp_mem_Gam a) (monGrp_mem_Gam b)
      have hcongr : (mlt N (monGrp X a) * mlt N (monGrp X b)
            - mlt N (monGrp X b) * mlt N (monGrp X a))
          - (Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
            - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a))
          ∈ filq X N (Magma.size a + Magma.size b + 1) := by
        have h1 : mlt N (monGrp X a) * mlt N (monGrp X b)
            - Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
            ∈ filq X N (Magma.size a + Magma.size b + 1) := by
          have hA := filq_antitone X N
            (by omega : Magma.size a + Magma.size b + 1 ≤ (Magma.size a + 1) + Magma.size b)
            (mul_mem_filq X N (Magma.size a + 1) (Magma.size b) ha hLTb)
          have hB := filq_antitone X N
            (by omega : Magma.size a + Magma.size b + 1 ≤ Magma.size a + (Magma.size b + 1))
            (mul_mem_filq X N (Magma.size a) (Magma.size b + 1) hBa hb)
          have heq : mlt N (monGrp X a) * mlt N (monGrp X b)
              - Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
              = (mlt N (monGrp X a) - Ideal.Quotient.mk (fil X N) (monBrk X a))
                  * mlt N (monGrp X b)
                + Ideal.Quotient.mk (fil X N) (monBrk X a)
                  * (mlt N (monGrp X b) - Ideal.Quotient.mk (fil X N) (monBrk X b)) := by
            noncomm_ring
          rw [heq]
          exact Submodule.add_mem _ hA hB
        have h2 : mlt N (monGrp X b) * mlt N (monGrp X a)
            - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a)
            ∈ filq X N (Magma.size a + Magma.size b + 1) := by
          have hA := filq_antitone X N
            (by omega : Magma.size a + Magma.size b + 1 ≤ (Magma.size b + 1) + Magma.size a)
            (mul_mem_filq X N (Magma.size b + 1) (Magma.size a) hb hLTa)
          have hB := filq_antitone X N
            (by omega : Magma.size a + Magma.size b + 1 ≤ Magma.size b + (Magma.size a + 1))
            (mul_mem_filq X N (Magma.size b) (Magma.size a + 1) hBb ha)
          have heq : mlt N (monGrp X b) * mlt N (monGrp X a)
              - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a)
              = (mlt N (monGrp X b) - Ideal.Quotient.mk (fil X N) (monBrk X b))
                  * mlt N (monGrp X a)
                + Ideal.Quotient.mk (fil X N) (monBrk X b)
                  * (mlt N (monGrp X a) - Ideal.Quotient.mk (fil X N) (monBrk X a)) := by
            noncomm_ring
          rw [heq]
          exact Submodule.add_mem _ hA hB
        have heq2 : (mlt N (monGrp X a) * mlt N (monGrp X b)
              - mlt N (monGrp X b) * mlt N (monGrp X a))
            - (Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
              - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a))
            = (mlt N (monGrp X a) * mlt N (monGrp X b)
                - Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b))
              - (mlt N (monGrp X b) * mlt N (monGrp X a)
                - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a)) := by
            noncomm_ring
        rw [heq2]
        exact Submodule.sub_mem _ h1 h2
      have hsum : mlt N ⁅monGrp X a, monGrp X b⁆
            - (Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
              - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a))
            ∈ filq X N (Magma.size a + Magma.size b + 1) := by
        have heq : mlt N ⁅monGrp X a, monGrp X b⁆
              - (Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
                - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a))
              = (mlt N ⁅monGrp X a, monGrp X b⁆
                  - (mlt N (monGrp X a) * mlt N (monGrp X b)
                    - mlt N (monGrp X b) * mlt N (monGrp X a)))
                + ((mlt N (monGrp X a) * mlt N (monGrp X b)
                    - mlt N (monGrp X b) * mlt N (monGrp X a))
                  - (Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
                    - Ideal.Quotient.mk (fil X N) (monBrk X b)
                      * Ideal.Quotient.mk (fil X N) (monBrk X a))) := by
            noncomm_ring
        rw [heq]
        exact Submodule.add_mem _ hcomm hcongr
      rw [monGrp_mul, monBrk_mul, Magma.size_mul, map_sub, map_mul, map_mul]
      exact hsum

theorem mlt_monGrp_sub_mem (X : Type) (N : ℕ) (c : Work.SSGRoute.prop5.Magma X)
    (hN : Work.SSGRoute.prop5.Magma.size c + 1 ≤ N) :
    Work.SSGRoute.prop5.lctf.mlt N (Work.SSGRoute.prop5.lctf.monGrp X c) -
      Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X N)
        (Work.SSGRoute.prop5.monBrk X c) ∈
      Work.SSGRoute.prop5.filq X N (Work.SSGRoute.prop5.Magma.size c + 1) :=
  mlt_monGrp_sub_mem_aux X c N hN

end Work.SSGRoute.prop5.lctf
