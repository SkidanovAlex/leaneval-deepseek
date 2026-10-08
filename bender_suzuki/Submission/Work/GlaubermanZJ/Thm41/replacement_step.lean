import Mathlib
import Submission.Work.GlaubermanZJ.cor3_1
import Submission.Work.GlaubermanZJ.isAbelianSubgroup_iff
import Submission.Work.PGroup.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GlaubermanZJ.Thm41

open scoped commutatorElement

/-- If two subgroups `H K` of a group commute elementwise, then every element of the join
`H ⊔ K` is a product `h * k` with `h ∈ H`, `k ∈ K`.

(For arbitrary subgroups an element of `H ⊔ K` is only a finite alternating word; elementwise
commutation lets the `H`- and `K`-parts be gathered.) -/
theorem exists_mul_mem_sup_of_commute {G : Type*} [Group G] {H K : Subgroup G}
    (h : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G} (hx : x ∈ H ⊔ K) :
    ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  have hsub : (H ⊔ K : Subgroup G) ≤
      { carrier := {x : G | ∃ h ∈ H, ∃ k ∈ K, h * k = x}
        mul_mem' := by
          rintro a b ⟨h1, hh1, k1, hk1, rfl⟩ ⟨h2, hh2, k2, hk2, rfl⟩
          refine ⟨h1 * h2, H.mul_mem hh1 hh2, k1 * k2, K.mul_mem hk1 hk2, ?_⟩
          simp only [mul_assoc]
          rw [← mul_assoc h2 k1 k2, h h2 hh2 k1 hk1]
          group
        one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
        inv_mem' := by
          rintro a ⟨h1, hh1, k1, hk1, rfl⟩
          refine ⟨h1⁻¹, H.inv_mem hh1, k1⁻¹, K.inv_mem hk1, ?_⟩
          rw [h h1⁻¹ (H.inv_mem hh1) k1⁻¹ (K.inv_mem hk1)]
          group } := by
    apply sup_le
    · intro h1 hh1; exact ⟨h1, hh1, 1, K.one_mem, by simp⟩
    · intro k1 hk1; exact ⟨1, H.one_mem, k1, hk1, by simp⟩
  exact hsub hx

/-- The final step of Glauberman's Theorem 4.1: with `M = commClosure x A ≤ S` abelian, `M ≤ B`, `M ⊄ A`, `A ∩ B` centralizing `M` and `[M,A,A] = 1`, the subgroup `M ⊔ (A ⊓ C(M))` is abelian of maximal order in `S`, meets `B` strictly more than `A` does, and satisfies `[A*,A,A] = 1`. -/
theorem replacement_step {G : Type*} [Group G] {S A B : Subgroup G} [Finite S] {x : G}
    (hA : Work.GlaubermanZJ.IsMaxAbelianSubgroup S A)
    (hMle : Work.PGroup.commClosure x A ≤ S)
    (hMab : IsMulCommutative (Work.PGroup.commClosure x A))
    (hMB : Work.PGroup.commClosure x A ≤ B)
    (hMnotA : ¬ Work.PGroup.commClosure x A ≤ A)
    (hcent : A ⊓ B ≤ Subgroup.centralizer ((Work.PGroup.commClosure x A : Subgroup G) : Set G))
    (hMAA : ⁅⁅Work.PGroup.commClosure x A, A⁆, A⁆ = ⊥) :
    ∃ A' : Subgroup G, Work.GlaubermanZJ.IsMaxAbelianSubgroup S A' ∧ A ⊓ B < A' ⊓ B ∧
      ⁅⁅A', A⁆, A⁆ = ⊥ := by
  -- Destructure the maximality hypothesis and pass to the `Work.PGroup` vocabulary.
  obtain ⟨hAS, hAab, hAcard⟩ := (Work.GlaubermanZJ.isMaxAbelianSubgroup_iff S A).mp hA
  have hAcom : IsMulCommutative ↥A := Work.GlaubermanZJ.isAbelianSubgroup_iff.mp hAab
  -- Thompson's product lemma: `M ⊔ (A ⊓ C(M))` is abelian of order `maxAbelianOrder S`.
  obtain ⟨hA'ab, hA'card⟩ :=
    Work.PGroup.thompson_product_centralizer (P := S) (A := A) (x := x)
      hAS hAcom hAcard hMle hMab
  refine ⟨Work.PGroup.commClosure x A ⊔
      (A ⊓ Subgroup.centralizer (Work.PGroup.commClosure x A : Set G)), ?_, ?_, ?_⟩
  · -- `M ⊔ (A ⊓ C(M))` is a maximal abelian subgroup of `S`.
    rw [Work.GlaubermanZJ.isMaxAbelianSubgroup_iff]
    exact ⟨sup_le hMle (inf_le_left.trans hAS),
      Work.GlaubermanZJ.isAbelianSubgroup_iff.mpr hA'ab, hA'card⟩
  · -- `A ⊓ B < (M ⊔ (A ⊓ C(M))) ⊓ B`.
    refine lt_of_le_not_ge ?_ ?_
    · -- `A ⊓ B ≤ M ⊔ (A ⊓ C(M))` since `A ⊓ B ≤ A ⊓ C(M)`.
      exact le_inf ((le_inf inf_le_left hcent).trans le_sup_right) inf_le_right
    · -- `(M ⊔ (A ⊓ C(M))) ⊓ B ≰ A ⊓ B`, because `M ≤ B` and `M ⊄ A`.
      intro hle
      exact hMnotA ((le_inf le_sup_left hMB).trans (hle.trans inf_le_left))
  · -- `[A*,A,A] = 1`, via `[A*, A] = [M, A]`.
    refine le_bot_iff.mp ?_
    have hMAA' : ⁅Work.PGroup.commClosure x A, A⁆ ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMAA
    have hcomm_le : ⁅Work.PGroup.commClosure x A ⊔
        (A ⊓ Subgroup.centralizer (Work.PGroup.commClosure x A : Set G)), A⁆ ≤
        ⁅Work.PGroup.commClosure x A, A⁆ := by
      rw [Subgroup.commutator_le]
      intro g hg a ha
      -- `g ∈ M ⊔ C` decomposes as `m * n` with `m ∈ M`, `n ∈ A ⊓ C(M)`.
      obtain ⟨m, hm, n, hn, rfl⟩ :=
        exists_mul_mem_sup_of_commute
          (H := Work.PGroup.commClosure x A)
          (K := A ⊓ Subgroup.centralizer (Work.PGroup.commClosure x A : Set G))
          (fun m hm n hn => Subgroup.mem_centralizer_iff.mp hn.2 m hm) hg
      have hnA : n ∈ A := hn.1
      -- `[n, a] = 1` because `n, a` lie in the abelian subgroup `A`.
      have hn1 : ⁅n, a⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        simpa using congrArg Subtype.val (isMulCommutative_iff.mp hAcom ⟨n, hnA⟩ ⟨a, ha⟩)
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hgoal : m * ⁅n, a⁆ * m⁻¹ * ⁅m, a⁆ = ⁅m, a⁆ := by rw [hn1]; group
      rw [hgoal]
      exact Subgroup.commutator_mem_commutator hm ha
    exact (Subgroup.commutator_mono hcomm_le le_rfl).trans_eq hMAA

end Work.GlaubermanZJ.Thm41
