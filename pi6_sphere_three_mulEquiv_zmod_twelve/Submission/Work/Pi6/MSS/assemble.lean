import Mathlib
import Submission.Work.Pi6.MSS.AssembleDefs
import Submission.Work.Pi6.MSS.AssembleCore
import Submission.Work.Pi6.MSS.mssMulLeib
import Submission.Work.Pi6.MSS.mssProjKer
import Submission.Work.Pi6.MSS.mssProjMul
import Submission.Work.Pi6.MSS.mssMulCompat
import Submission.Work.Pi6.MSS.convPage
import Submission.Work.Pi6.MSS.pagesData
import Submission.Work.Pi6.MSS.PageData
import Submission.Work.Pi6.MSS.Pages
import Submission.Work.Pi6.MSS.PagesComp
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits
open Classical
attribute [local instance] Classical.propDecidable

noncomputable section

variable (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜)

/-- The multiplicative cohomological Serre spectral sequence of a filtered cochain complex with a
product, assembled from the concrete pages. -/
def mssSS (D : PagesData 𝕜 W) : CohSS 𝕜 where
  E := fun r a => mssE 𝕜 W r a
  d := fun r a b => mssD 𝕜 W r a b
  d_shape := fun r a b h => mssD_shape 𝕜 W r a b h
  d_comp := fun r a b c => mssD_comp 𝕜 W r a b c
  quad := fun r a h => isZero_mssE 𝕜 W r h
  proj := fun r a => mssProj 𝕜 W r a
  proj_surj := fun r a hr => mssProj_surj 𝕜 W r a hr
  proj_ker := fun r a hr x => mssProjKer 𝕜 W r a hr x
  mul := fun r a b c h => mssMul 𝕜 W r a b c h
  mul_congr := fun r a b c h1 h2 x y => mssMul_congr 𝕜 W r a b c h1 h2 x y
  leibniz := fun r a b c h x y hr => mssMulLeib 𝕜 W r hr a b c h x y
  proj_mul := fun r a b c h x y z hr hz => mssProjMul 𝕜 W r hr a b c h x y z hz
  bot := fun r s => ModuleCat.ofHom (mssBot 𝕜 W r s)
  bot_spec := fun r s x hr => mssBot_spec 𝕜 W r s hr x
  col := fun r q => ModuleCat.ofHom (mssCol 𝕜 W r q)
  col_spec := fun r q x hr => mssCol_spec 𝕜 W r q hr x

/-- The normalization iso from the bidegree-indexed page to the concrete page. -/
lemma mssSS_E (D : PagesData 𝕜 W) (r : ℕ) (a : ℤ × ℤ) :
    (mssSS 𝕜 W D).E r a = mssE 𝕜 W r a := rfl

/-- The identification of the concrete page `pEraw 𝕜 W (n+2) s n` with the corresponding
bidegree `(s, n-s)` of the assembled spectral sequence. -/
lemma mssE_sum (n s : ℕ) (hs : s ≤ n) :
    mssE 𝕜 W (n + 2) ((s : ℤ), ((n - s : ℕ) : ℤ)) = pEraw 𝕜 W (n + 2) s n := by
  show pEraw 𝕜 W (n + 2) (EI ((s : ℤ), ((n - s : ℕ) : ℤ)))
      (EN ((s : ℤ), ((n - s : ℕ) : ℤ))) = pEraw 𝕜 W (n + 2) s n
  rw [EI_pair, EN_pair, show s + (n - s) = n from by omega]

/-- The assembled data of the spectral sequence of a filtered cochain complex with a product. -/
def mssAssembled (D : PagesData 𝕜 W) : Assembled 𝕜 W D where
  S := mssSS 𝕜 W D
  iso := fun r s q _ => mssNorm 𝕜 W r s q
  mul_compat := fun r s q s' q' hr x y => mssMulCompat 𝕜 W D r s q s' q' hr x y
  zero := by
    intro n s hs hsub
    rw [mssSS_E, mssE_sum 𝕜 W n s hs]
    exact ModuleCat.isZero_of_subsingleton _
  finrank_sum := by
    intro n
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hs' : s ≤ n := by have := Finset.mem_range.mp hs; omega
    rw [mssSS_E, mssE_sum 𝕜 W n s hs']

theorem assemble (𝕜 : Type) [Field 𝕜] (W : Work.Pi6.MSS.CohFilt 𝕜)
    (D : Work.Pi6.MSS.PagesData 𝕜 W) :
    Nonempty (Work.Pi6.MSS.Assembled 𝕜 W D) :=
  ⟨mssAssembled 𝕜 W D⟩

end

end Work.Pi6.MSS
