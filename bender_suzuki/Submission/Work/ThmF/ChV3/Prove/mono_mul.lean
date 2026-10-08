import Mathlib
import Submission.Work.ThmF.ChV3.Prove.pow_swap

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

/-- Normal form for the product of two elements of the form `c^a * u^b * v^d`,
using the relation `u * v = c * (v * u)` together with the centrality of `c`
on `u` and `v` (`pow_swap` supplies the swap `v^d * u^b' = c^(-(d*b')) * u^b' * v^d`). -/
lemma mono_mul {M : Type*} [Group M] (u v c : M)
    (huv : u * v = c * (v * u)) (hcu : Commute c u) (hcv : Commute c v)
    (a b d a' b' d' : ℤ) :
    (c^a * u^b * v^d) * (c^a' * u^b' * v^d') = c^(a + a' - d*b') * u^(b+b') * v^(d+d') := by
  have hX : Commute c (u^b * v^d) := (hcu.zpow_right b).mul_right (hcv.zpow_right d)
  have step1 : (c^a * u^b * v^d) * (c^a' * u^b' * v^d')
      = c^(a+a') * ((u^b * v^d) * (u^b' * v^d')) := by
    have h : (u^b * v^d) * c^a' = c^a' * (u^b * v^d) := (hX.symm.zpow_right a').eq
    calc (c^a * u^b * v^d) * (c^a' * u^b' * v^d')
        = c^a * (u^b * v^d) * (c^a' * (u^b' * v^d')) := by group
      _ = c^a * ((u^b * v^d) * c^a') * (u^b' * v^d') := by group
      _ = c^a * (c^a' * (u^b * v^d)) * (u^b' * v^d') := by rw [h]
      _ = c^(a+a') * ((u^b * v^d) * (u^b' * v^d')) := by group
  have step2 : (u^b * v^d) * (u^b' * v^d') = c^(-(d*b')) * (u^(b+b') * v^(d+d')) := by
    have h := pow_swap u v c huv hcu hcv d b'
    have hcomm : Commute (u^b) (c^(-(d*b'))) := (hcu.symm.zpow_left b).zpow_right (-(d*b'))
    calc (u^b * v^d) * (u^b' * v^d')
        = u^b * (v^d * u^b') * v^d' := by group
      _ = u^b * (c^(-(d*b')) * (u^b' * v^d)) * v^d' := by rw [h]
      _ = (u^b * c^(-(d*b'))) * ((u^b' * v^d) * v^d') := by group
      _ = (c^(-(d*b')) * u^b) * ((u^b' * v^d) * v^d') := by rw [hcomm.eq]
      _ = c^(-(d*b')) * (u^(b+b') * v^(d+d')) := by group
  calc (c^a * u^b * v^d) * (c^a' * u^b' * v^d')
      = c^(a+a') * ((u^b * v^d) * (u^b' * v^d')) := step1
    _ = c^(a+a') * (c^(-(d*b')) * (u^(b+b') * v^(d+d'))) := by rw [step2]
    _ = c^(a + a' - d*b') * u^(b+b') * v^(d+d') := by group

end Work.ThmF.ChV3.Prove
