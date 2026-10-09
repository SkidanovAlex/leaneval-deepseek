/-
Copyright (c) 2025. All rights reserved.

# Exactness of the inflation–restriction sequence in degree `1`

For a normal subgroup `N ◁ G` and a `G`-module `A` the inflation map
`infH1 : H¹(G ⧸ N, A^N) → H¹(G, A)` and the restriction map
`resH1 : H¹(G, A) → H¹(N, A)` fit into the exact sequence
`0 → H¹(G ⧸ N, A^N) → H¹(G, A) → H¹(N, A)`;
here we prove exactness at the middle term: the image of inflation is the kernel of
restriction.

## Main result

* `Work.GroupCohomology.range_infH1_eq_ker_resH1`
-/
import Mathlib
import Submission.Work.GroupCohomology.Inflation
import Submission.Work.GroupCohomology.Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- **Exactness of inflation–restriction in degree `1`.**  For a normal subgroup `N ◁ G` the
image of the inflation map `H¹(G ⧸ N, A^N) → H¹(G, A)` is the kernel of the restriction map
`H¹(G, A) → H¹(N, A)`. -/
theorem range_infH1_eq_ker_resH1 {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (N : Subgroup G) [N.Normal] :
    (Work.GroupCohomology.infH1 (A := A) N).range =
      (Work.GroupCohomology.resH1 (A := A) G N).ker := by
  apply le_antisymm
  · -- `im infH1 ≤ ker resH1`: the restriction of an inflated cocycle to `N` is a coboundary.
    intro y hy
    rw [AddMonoidHom.mem_range] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [AddMonoidHom.mem_ker]
    induction x using QuotientAddGroup.induction_on with
    | _ f =>
      rw [show (↑f : H1 (G ⧸ N) ↥(invariants (↥N) A)) =
          H1π (G ⧸ N) ↥(invariants (↥N) A) f from rfl, infH1_H1π, resH1_H1π]
      rw [H1π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
      rw [mem_B1_iff]
      refine ⟨0, ?_⟩
      funext n
      rw [d0_apply, smul_zero, sub_zero]
      show (0 : A) = (infCocycle1 N f : G → A) (n : G)
      rw [infCocycle1_apply]
      have hm : QuotientGroup.mk' N (n : G) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact n.2
      rw [hm]
      have h1 : (f : Z1 (G ⧸ N) ↥(invariants (↥N) A)).1 1 = 0 :=
        Z1.map_one (G ⧸ N) ↥(invariants (↥N) A) f.2
      simpa using (congrArg Subtype.val h1).symm
  · -- `ker resH1 ≤ im infH1`: an invariant cocycle representing a class killed by restriction.
    intro y hy
    rw [AddMonoidHom.mem_ker] at hy
    induction y using QuotientAddGroup.induction_on with
    | _ c =>
      rw [show (↑c : H1 G A) = H1π G A c from rfl, resH1_H1π] at hy
      rw [H1π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap,
          mem_B1_iff] at hy
      obtain ⟨a, ha⟩ := hy
      -- `ha : d⁰_{N} a = res_{N} c`, i.e. `c n = n • a - a` for every `n ∈ N`.
      have hcan : ∀ n : N, (n : G) • a - a = (c : G → A) (n : G) := by
        intro n
        have h := congrFun ha n
        simp only [d0_apply, AddSubgroup.subtype_apply] at h
        exact h
      -- The corrected cocycle `b = c - d⁰ a`; it takes values in `A^N` and is constant on
      -- cosets of `N`, hence is the inflation of a cocycle on `G ⧸ N` with values in `A^N`.
      let bZ : Z1 G A := c - ⟨d0 G A a, d0_mem_Z1 G A a⟩
      have hbval : ∀ g : G, (bZ : G → A) g = (c : G → A) g - (g • a - a) := fun _ => rfl
      have hb_zero : ∀ n : N, (bZ : G → A) (n : G) = 0 := by
        intro n
        rw [hbval, hcan n, sub_self]
      have hb_inv : ∀ g : G, (bZ : G → A) g ∈ invariants N A := by
        intro g
        rw [mem_invariants]
        intro n
        change (n : G) • (bZ : G → A) g = (bZ : G → A) g
        have h1 : (bZ : G → A) ((n : G) * g) = (n : G) • (bZ : G → A) g := by
          rw [bZ.2 (n : G) g, hb_zero n, add_zero]
        have hsplit : (n : G) * g = g * (g⁻¹ * (n : G) * g) := by group
        have hmem : g⁻¹ * (n : G) * g ∈ N := by
          simpa using (inferInstance : N.Normal).conj_mem (n : G) n.2 g⁻¹
        have h4 : (bZ : G → A) (g * (g⁻¹ * (n : G) * g)) = (bZ : G → A) g := by
          rw [bZ.2 g (g⁻¹ * (n : G) * g)]
          have hm : (bZ : G → A) (g⁻¹ * (n : G) * g) = 0 :=
            hb_zero ⟨g⁻¹ * (n : G) * g, hmem⟩
          rw [hm, smul_zero, zero_add]
        rw [← h1, hsplit, h4]
      have hfval_wd : ∀ p q : G, QuotientGroup.leftRel N p q →
          (⟨(bZ : G → A) p, hb_inv p⟩ : invariants N A) =
            ⟨(bZ : G → A) q, hb_inv q⟩ := by
        intro p q hpq
        rw [QuotientGroup.leftRel_apply] at hpq
        apply Subtype.ext
        show (bZ : G → A) p = (bZ : G → A) q
        rw [show q = p * (p⁻¹ * q) from by group]
        rw [bZ.2 p (p⁻¹ * q)]
        have hm : (bZ : G → A) (p⁻¹ * q) = 0 := hb_zero ⟨p⁻¹ * q, hpq⟩
        rw [hm, smul_zero, zero_add]
      let fval : G → invariants N A := fun g => ⟨(bZ : G → A) g, hb_inv g⟩
      let fbar : G ⧸ N → invariants N A := Quotient.lift fval hfval_wd
      have hfbar_mk : ∀ g : G, fbar (↑g : G ⧸ N) = fval g := by
        intro g
        show Quotient.lift fval hfval_wd (⟦g⟧) = fval g
        exact Quotient.lift_mk fval hfval_wd g
      have hfbar_cross : ∀ x z : G ⧸ N, fbar (x * z) = x • fbar z + fbar x := by
        intro x z
        induction x using QuotientGroup.induction_on with
        | _ g =>
          induction z using QuotientGroup.induction_on with
          | _ h =>
            rw [← QuotientGroup.mk_mul, hfbar_mk, hfbar_mk, hfbar_mk]
            apply Subtype.ext
            show (bZ : G → A) (g * h) = (g : G) • (bZ : G → A) h + (bZ : G → A) g
            rw [bZ.2 g h]
      let fcoc : Z1 (G ⧸ N) (invariants N A) := ⟨fbar, hfbar_cross⟩
      have hmkmk : ∀ g : G, fbar (QuotientGroup.mk' N g) = fval g := by
        intro g
        rw [QuotientGroup.mk'_apply]
        exact hfbar_mk g
      have hinf : ((infCocycle1 N fcoc : Z1 G A) : G → A) = (bZ : G → A) := by
        funext g
        rw [infCocycle1_apply]
        show (fbar (QuotientGroup.mk' N g) : A) = (bZ : G → A) g
        rw [show fbar (QuotientGroup.mk' N g) = fval g from hmkmk g]
      have hclass2 : (↑(infCocycle1 N fcoc) : H1 G A) = (↑c : H1 G A) := by
        rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_comap, mem_B1_iff]
        refine ⟨-a, ?_⟩
        funext g
        rw [d0_apply, map_sub]
        simp only [Pi.sub_apply, AddSubgroup.subtype_apply]
        rw [hinf, hbval, smul_neg]
        abel
      exact ⟨H1π (G ⧸ N) (invariants N A) fcoc, by rw [infH1_H1π]; exact hclass2⟩

end Work.GroupCohomology
