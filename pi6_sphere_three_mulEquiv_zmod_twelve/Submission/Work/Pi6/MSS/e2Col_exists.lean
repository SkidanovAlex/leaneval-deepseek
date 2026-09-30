import Mathlib
import Submission.Work.Pi6.MSS.e2Aux
import Submission.Work.Pi6.MSS.AssembleCore
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.convPage
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.MSS.assemble
import Submission.Work.Pi6.MSS.pagesData
import Submission.Work.Pi6.MSS.pageUnitSpec
import Submission.Work.Pi6.MSS.e2ColRho
import Submission.Work.Pi6.MSS.e2ColRho.mem_range_col_iff
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

/-- **The column (fibre-edge) map of the multiplicative Serre spectral sequence.**

For a Serre fibration `p : E → B` over a simply connected base, with fibre `F = p⁻¹(p e₀)` of finite
type through degree `N`, the zeroth column `E_2^{0,q}` of the multiplicative cohomological Serre
spectral sequence over a field `𝕜` is `H^q(F)`:

* the class of the unit cochain of `E` is the two-sided multiplicative unit of `E_2`;
* the identification is a ring map, i.e. it takes the cup product on the fibre to the page product;
* a class of the fibre is the restriction of a class of `E` exactly when it survives to `E_∞`, i.e.
  when it lies in the image of the iterated column inclusion `E_{q+2}^{0,q} → E_2^{0,q}`.

The map is the inverse of the restriction-to-the-fibre map `Work.Pi6.MSS.rhoSSEquiv` of
`Submission/Work/Pi6/MSS/e2ColRho.lean`.
-/
theorem e2Col_exists (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfin : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) :
    ∃ col : ∀ q : ℕ, q ≤ N → Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q →ₗ[𝕜]
        Work.Pi6.MSS.mssE 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)),
      Work.Pi6.MSS.mssPageUnit 𝕜 E B p
          (col 0 (Nat.zero_le N) (Work.Pi6.one 𝕜 (Work.StemsB.fibre p (p e₀)))) ∧
      (∀ (q q' : ℕ) (hq : q ≤ N) (hq' : q' ≤ N) (hqq : q + q' ≤ N)
        (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
        (f' : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q'),
        col (q + q') hqq (Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) q q' f f') =
          Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)) ((0 : ℤ), (q' : ℤ))
            ((0 : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp)
            (col q hq f) (col q' hq' f')) ∧
      (∀ (q : ℕ) (hq : q ≤ N) (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q),
        (∃ e : Work.Pi6.Coh 𝕜 E q,
            (Work.Pi6.cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) q).hom e = f) ↔
          ∃ z : Work.Pi6.MSS.mssE 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) (q + 2) ((0 : ℤ), (q : ℤ)),
            Work.Pi6.MSS.mssColIter 𝕜 E B p q q z = col q hq f) := by
  classical
  let col : ∀ q : ℕ, q ≤ N → Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q →ₗ[𝕜]
      mssE 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)) :=
    fun q hq => (rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin hq).symm.toLinearMap
  refine ⟨col, ?_, ?_, ?_⟩
  · exact colUnit_pageUnit 𝕜 E B p e₀ N hfib hconn hfin
  · intro q q' hq hq' hqq f f'
    change (rhoSSEquiv 𝕜 E B p e₀ N (q + q') hfib hconn hfin hqq).symm
        (Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) q q' f f') =
      mssMul 𝕜 (serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)) ((0 : ℤ), (q' : ℤ))
        ((0 : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp)
        ((rhoSSEquiv 𝕜 E B p e₀ N q hfib hconn hfin hq).symm f)
        ((rhoSSEquiv 𝕜 E B p e₀ N q' hfib hconn hfin hq').symm f')
    rw [LinearEquiv.symm_apply_eq,
      rhoSSEquiv_mul 𝕜 E B p e₀ N q q' hfib hconn hfin hq hq' hqq,
      LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  · intro q hq f
    exact Work.Pi6.MSS.e2ColRho.mem_range_col_iff 𝕜 E B p e₀ N q hfib hconn hfin hq f

end

end Work.Pi6.MSS
