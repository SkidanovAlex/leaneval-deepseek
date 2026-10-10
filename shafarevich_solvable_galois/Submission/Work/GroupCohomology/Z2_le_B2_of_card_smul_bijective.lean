import Mathlib.Tactic.Abel
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Group.Subgroup.Defs
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- If multiplication by `n = |G|` is bijective on the coefficient group `A`, then every `2`-cocycle of `G` is a coboundary: `Z²(G, A) ⊆ B²(G, A)`.  An explicit primitive for a cocycle `c` is the cochain `f` with `n • f g = ∑_{k : G} c (g, k)`. -/
theorem Z2_le_B2_of_card_smul_bijective {G : Type*} {A : Type*} [Group G] [Fintype G]
    [AddCommGroup A] [DistribMulAction G A]
    (hA : Function.Bijective (fun a : A => Fintype.card G • a)) :
    Work.GroupCohomology.Z2 G A ≤ Work.GroupCohomology.B2 G A := by
  intro c hc
  -- The additive endomorphism `a ↦ |G| • a` of `A`, which is bijective by hypothesis.
  let m : A →+ A :=
    { toFun := fun a => Fintype.card G • a
      map_zero' := by simp
      map_add' := fun a b => nsmul_add a b (Fintype.card G) }
  have hm : Function.Bijective m := hA
  let e : A ≃+ A := AddEquiv.ofBijective m hm
  have he : ∀ a : A, e a = Fintype.card G • a := fun a => rfl
  -- The endomorphism is `G`-equivariant.
  have he_smul : ∀ (g : G) (a : A), e (g • a) = g • e a := by
    intro g a
    rw [he, he]
    exact (map_nsmul (DistribMulAction.toAddMonoidEnd G A g) (Fintype.card G) a).symm
  -- The cocycle condition.
  have hcc : ∀ a b d : G, c (a * b, d) + c (a, b) = a • c (b, d) + c (a, b * d) :=
    (mem_Z2_iff G A c).mp hc
  -- Key averaging identity: `|G| • c (g, h) = g • S_h - S_{g h} + S_g`.
  have hkey : ∀ g h : G,
      g • (∑ k : G, c (h, k)) - (∑ k : G, c (g * h, k)) + (∑ k : G, c (g, k))
        = Fintype.card G • c (g, h) := by
    intro g h
    have hterm : ∀ k : G, g • c (h, k) = c (g * h, k) + c (g, h) - c (g, h * k) := by
      intro k
      rw [eq_sub_iff_add_eq]
      exact (hcc g h k).symm
    have h1 : g • (∑ k : G, c (h, k)) = ∑ k : G, g • c (h, k) := by
      rw [Finset.smul_sum]
    have h2 : (∑ k : G, g • c (h, k))
        = ∑ k : G, (c (g * h, k) + c (g, h) - c (g, h * k)) :=
      Finset.sum_congr rfl (fun k _ => hterm k)
    have h3 : (∑ k : G, (c (g * h, k) + c (g, h) - c (g, h * k)))
        = (∑ k : G, c (g * h, k)) + (∑ k : G, c (g, h)) - (∑ k : G, c (g, h * k)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h4 : (∑ k : G, c (g, h)) = Fintype.card G • c (g, h) := by
      rw [Finset.sum_const, Finset.card_univ]
    have h5 : (∑ k : G, c (g, h * k)) = ∑ k : G, c (g, k) :=
      Fintype.sum_equiv (Equiv.mulLeft h) (fun k => c (g, h * k)) (fun k => c (g, k))
        (fun k => rfl)
    have hmain : g • (∑ k : G, c (h, k))
        = (∑ k : G, c (g * h, k)) + Fintype.card G • c (g, h) - (∑ k : G, c (g, k)) := by
      rw [h1, h2, h3, h4, h5]
    rw [hmain]; abel
  -- The primitive cochain: `f g` is the unique `a` with `|G| • a = ∑_k c (g, k)`.
  let f : G → A := fun g => e.symm (∑ k : G, c (g, k))
  have hf : ∀ g : G, e (f g) = ∑ k : G, c (g, k) :=
    fun g => e.apply_symm_apply (∑ k : G, c (g, k))
  refine (mem_B2_iff G A c).mpr ⟨f, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  show d1 G A f (g, h) = c (g, h)
  rw [d1_apply]
  refine e.injective ?_
  have hgoal : e (g • f h - f (g * h) + f g) = e (c (g, h)) := by
    rw [AddEquiv.map_add, AddEquiv.map_sub, he_smul, hf, hf, hf, he]
    exact hkey g h
  exact hgoal

end Work.GroupCohomology
