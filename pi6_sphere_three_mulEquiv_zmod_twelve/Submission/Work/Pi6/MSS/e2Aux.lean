import Mathlib
import Submission.Work.Pi6.MSS.Pages
import Submission.Work.Pi6.MSS.PageData
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.AssembleCore
import Submission.Work.Pi6.MSS.assemble
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-- Iterated bottom-row projection `E_2^{s,0} → E_{k+2}^{s,0}`. -/
def mssBotIter (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (s : ℕ) :
    (k : ℕ) → mssE 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) →ₗ[𝕜]
      mssE 𝕜 (serreCF 𝕜 E B p) (k + 2) ((s : ℤ), (0 : ℤ))
  | 0 => LinearMap.id
  | k + 1 => (mssBot 𝕜 (serreCF 𝕜 E B p) (k + 2) (s : ℤ)).comp (mssBotIter E B p s k)

/-- Iterated zeroth-column inclusion `E_{k+2}^{0,q} → E_2^{0,q}`. -/
def mssColIter (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (q : ℕ) :
    (k : ℕ) → mssE 𝕜 (serreCF 𝕜 E B p) (k + 2) ((0 : ℤ), (q : ℤ)) →ₗ[𝕜]
      mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ))
  | 0 => LinearMap.id
  | k + 1 => (mssColIter E B p q k).comp (mssCol 𝕜 (serreCF 𝕜 E B p) (k + 2) (q : ℤ))

/-- An element of the page `E_2^{0,0}` is the two-sided multiplicative unit of the page. -/
def mssPageUnit (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (u : mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (0 : ℤ))) : Prop :=
  (∀ (s q : ℕ) (x : mssE 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (q : ℤ))),
      mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (0 : ℤ)) ((s : ℤ), (q : ℤ)) ((s : ℤ), (q : ℤ))
        (by ext <;> simp) u x = x) ∧
  (∀ (s q : ℕ) (x : mssE 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (q : ℤ))),
      mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((s : ℤ), (q : ℤ)) ((0 : ℤ), (0 : ℤ)) ((s : ℤ), (q : ℤ))
        (by ext <;> simp) x u = x)


namespace E2Aux

/-- The iterated bottom-row map of `mssSS` is `mssBotIter`. -/
theorem botTo_eq_mssBotIter (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (D : PagesData 𝕜 (serreCF 𝕜 E B p)) (s : ℕ) :
    ∀ k : ℕ, (CohSS.botTo (mssSS 𝕜 (serreCF 𝕜 E B p) D) (s : ℤ) k).hom
        = mssBotIter 𝕜 E B p s k
  | 0 => rfl
  | k + 1 => by
      rw [CohSS.botTo, mssBotIter, ModuleCat.hom_comp, E2Aux.botTo_eq_mssBotIter 𝕜 E B p D s k]
      rfl

/-- The iterated column-`0` map of `mssSS` is `mssColIter`. -/
theorem colTo_eq_mssColIter (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (D : PagesData 𝕜 (serreCF 𝕜 E B p)) (q : ℕ) :
    ∀ k : ℕ, (CohSS.colTo (mssSS 𝕜 (serreCF 𝕜 E B p) D) (q : ℤ) k).hom
        = mssColIter 𝕜 E B p q k
  | 0 => rfl
  | k + 1 => by
      rw [CohSS.colTo, mssColIter, ModuleCat.hom_comp,
        E2Aux.colTo_eq_mssColIter 𝕜 E B p D q k]
      rfl

/-- The product of `mssSS` at `r` is `mssMul`. -/
theorem mssSS_mul_apply (𝕜 : Type) [Field 𝕜] {W : CohFilt 𝕜} {D : PagesData 𝕜 W}
    (r : ℕ) (a b c : ℤ × ℤ) (h : a + b = c) (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) :
    (mssSS 𝕜 W D).mul r a b c h x y = mssMul 𝕜 W r a b c h x y := rfl

end E2Aux

end

end Work.Pi6.MSS
