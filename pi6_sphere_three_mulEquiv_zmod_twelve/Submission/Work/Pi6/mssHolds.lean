import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.MSS.Defs
import Submission.Work.Pi6.MSS.CohFilt
import Submission.Work.Pi6.MSS.Pages
import Submission.Work.Pi6.MSS.PageData
import Submission.Work.Pi6.MSS.serreCohFilt
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.CohBridge
import Submission.Work.Pi6.MSS.PagesComp
import Submission.Work.Pi6.MSS.pagesData
import Submission.Work.Pi6.MSS.convPage
import Submission.Work.Pi6.MSS.AssembleDefs
import Submission.Work.Pi6.MSS.AssembleCore
import Submission.Work.Pi6.MSS.assemble
import Submission.Work.Pi6.MSS.convFin
import Submission.Work.Pi6.MSS.e2Add
import Submission.Work.Pi6.MSS.e2Mul
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Area MSS (crux B): the multiplicative cohomological Serre spectral sequence over a field

The assembly of the proof of `Work.Pi6.MSSHolds`: for a Serre fibration `p : E → B` over a simply
connected base with base and fibre cohomology finite-dimensional through degree `N`, the concrete
cochain-level Serre spectral sequence of the filtered cochain complex
`Work.Pi6.MSS.serreCF 𝕜 E B p` (the singular cochains of `E` filtered by the skeleta of `B`, with
the Alexander–Whitney cup product) is a `Work.Pi6.CohSS` satisfying `Work.Pi6.IsSerreMSS`:

* the pages are the standard ones (`Work.Pi6.MSS.pEraw`, assembled into a `CohSS` by
  `Work.Pi6.MSS.assemble`);
* `E_2^{s,q} ≅ H^s(B;𝕜) ⊗ H^q(F;𝕜)` multiplicatively (`Work.Pi6.MSS.e2Add`,
  `Work.Pi6.MSS.e2Mul`);
* convergence in total degree `≤ N` and the two edge maps (`Work.Pi6.MSS.convPage`,
  `Work.Pi6.MSS.convFin`, and the edge clauses of `Work.Pi6.MSS.e2Mul`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6

noncomputable section

theorem mssHolds : Work.Pi6.MSSHolds := by
  intro 𝕜 _ E B _ _ p e₀ N hfib hconn hfinF hfinB
  classical
  -- the filtered cochain complex of the Serre filtration
  set W : Work.Pi6.MSS.CohFilt 𝕜 := Work.Pi6.MSS.serreCF 𝕜 E B p with hW
  -- the pages and the concrete assembled spectral sequence
  obtain ⟨D⟩ := Work.Pi6.MSS.pagesData 𝕜 W
  -- the E₂ identification with its multiplicativity and the two edge properties
  obtain ⟨e2, hmul, hbase, hfibre⟩ :=
    Work.Pi6.MSS.e2Mul 𝕜 E B p e₀ N hfib hconn hfinF D
  refine ⟨Work.Pi6.MSS.mssSS 𝕜 W D, e2, ?_, ?_, ?_, ?_, ?_⟩
  · -- multiplicativity of the E₂ page
    intro s q s' q' b f b' f' hs hq
    exact hmul s q s' q' (by omega) (by omega) (by omega) (by omega) b f b' f' hs hq
  · -- vanishing in total degree `n ≤ N`
    intro n _ hnN hsub s q hsq
    have hs : s ≤ n := by omega
    have hfin : Module.Finite 𝕜 (W.C.homology n) :=
      (Work.Pi6.MSS.convFin 𝕜 E B p e₀ N hfib hconn hfinB hfinF n hnN).1
    have hsub' : Subsingleton (Work.Pi6.MSS.pEraw 𝕜 W (n + 2) s n) :=
      (Work.Pi6.MSS.convPage 𝕜 W n hfin).1 s hs hsub
    have hA := (Work.Pi6.MSS.mssAssembled 𝕜 W D).zero n s hs hsub'
    have hidx : ((s : ℤ), (q : ℤ)) = ((s : ℤ), ((n - s : ℕ) : ℤ)) := by
      congr 1
      omega
    rwa [hidx]
  · -- the dimension identity in total degree `n ≤ N`
    intro n hnN
    have hcf := Work.Pi6.MSS.convFin 𝕜 E B p e₀ N hfib hconn hfinB hfinF n hnN
    calc (∑ s ∈ Finset.range (n + 1),
            Module.finrank 𝕜 ((Work.Pi6.MSS.mssSS 𝕜 W D).E (n + 2)
              ((s : ℤ), ((n - s : ℕ) : ℤ))))
        = ∑ s ∈ Finset.range (n + 1),
            Module.finrank 𝕜 (Work.Pi6.MSS.pEraw 𝕜 W (n + 2) s n) :=
          (Work.Pi6.MSS.mssAssembled 𝕜 W D).finrank_sum n
      _ = Module.finrank 𝕜 (W.C.homology n) := hcf.2
      _ = Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 E n) := by
          rw [Work.Pi6.MSS.serreCF_homology]
  · -- the base edge map
    exact hbase
  · -- the fibre edge map
    exact hfibre

end

end Work.Pi6
