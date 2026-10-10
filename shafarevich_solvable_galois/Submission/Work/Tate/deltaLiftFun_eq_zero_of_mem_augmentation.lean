import Mathlib.Analysis.Normed.Group.Uniform
import Submission.Work.Tate.SES
import Submission.Work.Tate.map_augmentation_eq_of_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

theorem deltaLiftFun_eq_zero_of_mem_augmentation {G : Type*} {A : Type*} {B : Type*}
    {C : Type*} [Group G] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C] [Fintype G]
    (S : Work.Tate.SES G A B C) {x : C} (hx : x ∈ Work.Tate.augmentation G C) :
    S.deltaLiftFun ⟨x, Work.Tate.augmentation_le_ker_norm hx⟩ = 0 := by
  -- Since `g` is surjective and `G`-equivariant, `x` is the image of an element of the
  -- augmentation submodule of `B`.
  have hmap : x ∈ (augmentation G B).map S.g := by
    rw [map_augmentation_eq_of_surjective S.g S.g_equiv S.g_surjective]
    exact hx
  obtain ⟨b, hb_mem, hb_eq⟩ := AddSubgroup.mem_map.mp hmap
  -- Such an element is killed by the norm.
  have hb_norm : norm G B b = 0 := norm_eq_zero_of_mem_augmentation hb_mem
  -- Hence `sec x - b` lies in the kernel of `g`, i.e. in the image of `f`.
  have hker : S.g (S.sec x - b) = 0 := by
    rw [map_sub, S.sec_spec x, hb_eq, sub_self]
  obtain ⟨a₀, ha₀⟩ := S.exists_of_g_eq_zero hker
  -- Therefore the canonical preimage of `x` is a norm.
  have hpre : S.preimage ⟨x, augmentation_le_ker_norm hx⟩ = norm G A a₀ := by
    apply S.f_injective
    rw [S.f_preimage]
    have h1 : S.sec x = b + S.f a₀ := by rw [ha₀]; abel
    rw [h1, map_add, hb_norm, zero_add, norm_map S.f S.f_equiv a₀]
  have h2 : S.deltaLiftFun ⟨x, augmentation_le_ker_norm hx⟩ = H0π G A (normToFixed G A a₀) := by
    rw [deltaLiftFun_apply S]
    exact congrArg (H0π G A) (Subtype.ext hpre)
  rw [h2]
  exact (H0π_eq_zero_iff (normToFixed G A a₀)).mpr ⟨a₀, rfl⟩

end Work.Tate
