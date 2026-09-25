import Mathlib
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
import Submission.NK.GlobalCFT.NormGroup

namespace NK.CFTLib.Existence

theorem normIdeleHom_congruenceSubgroup_le {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (m : ℕ) (hm : 0 < m) (z : NK.GlobalCFT.Idele L) (hz : z ∈ NK.CFTLib.Arl.congruenceSubgroup L m) : NK.GlobalCFT.Idele.normIdeleHom K L z ∈ NK.CFTLib.Arl.congruenceSubgroup K m :=
  NK.CFTLib.Arl.normIdeleHom_mem_congruenceSubgroup m hm hz

end NK.CFTLib.Existence
