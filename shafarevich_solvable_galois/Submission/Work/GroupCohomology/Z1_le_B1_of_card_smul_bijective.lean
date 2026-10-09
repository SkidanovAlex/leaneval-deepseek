import Mathlib
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

open Finset

/-- If multiplication by `n = |G|` is bijective on the coefficient group `A`, then every `1`-cocycle of `G` is a coboundary: `Z¹(G, A) ⊆ B¹(G, A)`.  An explicit primitive for a cocycle `f` is the (unique) `a` with `n • a = -∑_{g : G} f g`. -/
theorem Z1_le_B1_of_card_smul_bijective {G : Type*} {A : Type*} [Group G] [Fintype G]
    [AddCommGroup A] [DistribMulAction G A]
    (hA : Function.Bijective (fun a : A => Fintype.card G • a)) :
    Work.GroupCohomology.Z1 G A ≤ Work.GroupCohomology.B1 G A := by
  intro f hf
  rw [mem_Z1_iff] at hf
  -- `b` is the sum of the values of the cocycle, `a` the primitive of `-b`.
  set b : A := ∑ g : G, f g with hb
  obtain ⟨a, ha⟩ := hA.2 (-b)
  have ha' : Fintype.card G • a = -b := ha
  rw [mem_B1_iff]
  refine ⟨a, ?_⟩
  funext g
  simp only [d0_apply]
  -- it suffices to prove the equality after multiplying by `|G|`
  have hinj : Function.Injective (fun a : A => Fintype.card G • a) := hA.1
  apply hinj
  -- `g • b = b - |G| • f g`, because `h ↦ g * h` permutes `G`
  have hgsmul : g • b = b - Fintype.card G • f g := by
    have h1 : g • b = ∑ h : G, g • f h := by
      rw [hb, Finset.smul_sum]
    have h2 : ∀ h : G, g • f h = f (g * h) - f g := by
      intro h
      rw [hf g h]; abel
    rw [h1, Finset.sum_congr rfl (fun h _ => h2 h), Finset.sum_sub_distrib]
    have h3 : ∑ h : G, f (g * h) = b := by
      rw [hb]
      simpa using (Equiv.sum_comp (Equiv.mulLeft g) f)
    have h4 : ∑ h : G, f g = Fintype.card G • f g := by
      simp [Finset.sum_const]
    rw [h3, h4]
  have hnsmul : Fintype.card G • (g • a) = g • (Fintype.card G • a) :=
    ((DistribSMul.toAddMonoidHom A g).map_nsmul (Fintype.card G) a).symm
  calc Fintype.card G • (g • a - a)
      = Fintype.card G • (g • a) - Fintype.card G • a := by rw [nsmul_sub]
    _ = g • (Fintype.card G • a) - Fintype.card G • a := by rw [hnsmul]
    _ = g • (-b) - (-b) := by rw [ha']
    _ = b - g • b := by rw [smul_neg]; abel
    _ = Fintype.card G • f g := by rw [hgsmul]; abel

end Work.GroupCohomology
