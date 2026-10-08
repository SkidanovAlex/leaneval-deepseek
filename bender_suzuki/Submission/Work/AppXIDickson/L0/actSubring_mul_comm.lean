import Mathlib
import Submission.Work.AppXIField.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.AppXIDickson.L0

open Work.AppXIField

/-- The generators `actEnd A V a` of `actSubring A V` commute pairwise: `A` is a commutative
group, so `a • (b • v) = b • (a • v)`. -/
theorem actEnd_commute (A V : Type*) [CommGroup A] [AddCommGroup V] [DistribMulAction A V]
    (a b : A) : Commute (actEnd A V a) (actEnd A V b) := by
  rw [Commute]
  ext v
  show (actEnd A V a * actEnd A V b) v = (actEnd A V b * actEnd A V a) v
  rw [show (actEnd A V a * actEnd A V b) v = a • (b • v) from rfl,
    show (actEnd A V b * actEnd A V a) v = b • (a • v) from rfl]
  rw [smul_smul, smul_smul, mul_comm]

theorem actSubring_mul_comm (A V : Type*) [CommGroup A] [AddCommGroup V] [DistribMulAction A V]
    (r s : ↥(Work.AppXIField.actSubring A V)) : r * s = s * r := by
  have hcomm : (Set.range (actEnd A V)).Pairwise Commute := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ -
    exact actEnd_commute A V a b
  exact (Subring.isMulCommutative_closure hcomm).is_comm.comm r s

end Work.AppXIDickson.L0
