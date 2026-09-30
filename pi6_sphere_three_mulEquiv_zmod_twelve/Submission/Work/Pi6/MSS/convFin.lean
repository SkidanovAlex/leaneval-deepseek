import Mathlib
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.Pages
import Submission.Work.Pi6.MSS.PagesComp
import Submission.Work.Pi6.MSS.PageData
import Submission.Work.Pi6.MSS.convPage
import Submission.Work.Pi6.MSS.e2Add
import Submission.Work.Pi6.MSS.convPageFin
import Submission.Work.Pi6.MSS.convFiltrationFin
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port
/-!
# Finiteness and convergence in total degree `n` of the Serre spectral sequence

For a Serre fibration `p : E → B` over a simply connected base whose base and fibre cohomology is
finite dimensional through degree `N`, the cohomology `H^n(E;𝕜)` of the total space is finite
dimensional for `n ≤ N`, and the page `E_{n+2}` in total degree `n` (which is `E_∞` there) has row
dimensions summing to `dim H^n(E;𝕜)`.

* `Work.Pi6.MSS.convPage` gives the dimension identity *given* finiteness of `H^n`;
* the finiteness is obtained from the `E_2` identification `E_2^{s,q} ≅ H^s(B) ⊗ H^q(F)`
  (`Work.Pi6.MSS.e2Add`), the fact that the pages are subquotients of one another (`convPageFin`),
  the identification `E_{n+2}^{t,n} ≅ F^tH^n/F^{t+1}H^n` (`Work.Pi6.MSS.convE`) and the elementary
  lemma that a finite decreasing filtration with finite successive quotients has a finite top piece
  (`Work.Pi6.MSS.convFiltrationFin`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.MSS

noncomputable section

private theorem convFinDualFinite (𝕜 : Type) [Field 𝕜] (V : Type) [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 (V →ₗ[𝕜] 𝕜)] : FiniteDimensional 𝕜 V := by
  classical
  exact FiniteDimensional.of_injective (Module.Dual.eval 𝕜 V)
    ((Module.Free.chooseBasis 𝕜 V).eval_injective)

/-! ## Finiteness of the `E_2` page in the degrees we need -/

/-- **Finiteness of the `E_2` page.**  From the additive `E_2`-identification
`E_2^{s,q} ≅ H^s(B) ⊗ H^q(F)` (`e2Add`) and the finite-dimensionality of `H^s(B)`, `H^q(F)`. -/
theorem e2Fin (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfinB : ∀ s : ℕ, s ≤ N → FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 B s))
    (hfinF : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (s n : ℕ) (hs : s ≤ n) (hn : n ≤ N) :
    Module.Finite 𝕜 (pEraw 𝕜 (serreCF 𝕜 E B p) 2 s n) := by
  classical
  have hq : n - s ≤ N := by omega
  obtain ⟨e⟩ := e2Add 𝕜 E B p e₀ N hfib hconn hfinF s (n - s) (by omega) hq
  haveI : FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 B s) := hfinB s (by omega)
  haveI : FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) (n - s)) :=
    hfinF (n - s) hq
  exact Module.Finite.equiv (Iso.toLinearEquiv
    (e.symm ≪≫ pEcastN 𝕜 (serreCF 𝕜 E B p) 2 s (show s + (n - s) = n by omega)))

/-! ## The main assembly -/

/-- **Finiteness and convergence in total degree `n`**, given finiteness of the `E_2` page. -/
theorem convFinAux (𝕜 : Type) [Field 𝕜] (W : CohFilt 𝕜) (n : ℕ)
    (h2 : ∀ s : ℕ, s ≤ n → Module.Finite 𝕜 (pEraw 𝕜 W 2 s n)) :
    Module.Finite 𝕜 (W.C.homology n) ∧
      (∑ t ∈ Finset.range (n + 1),
          Module.finrank 𝕜 (pEraw 𝕜 W (n + 2) t n))
        = Module.finrank 𝕜 (W.C.homology n) := by
  classical
  have hom := convHomologyLocal 𝕜
  -- `E_{n+2}^{t,n} ≅ F^tH^n / F^{t+1}H^n` is finite dimensional
  have hgr : ∀ t : ℕ, t ≤ n →
      Module.Finite 𝕜 (↥(convCH hom W n t) ⧸
        Submodule.comap (convCH hom W n t).subtype (convCH hom W n (t + 1))) := by
    intro t ht
    obtain ⟨e⟩ := convE hom W n t ht
    haveI : Module.Finite 𝕜 (pEraw 𝕜 W (n + 2) t n) :=
      convPageFin 𝕜 W 2 (n + 2) t n le_rfl (by omega) (h2 t ht)
    exact Module.Finite.equiv e
  -- the filtration of `H^n` has finite steps
  have hA0 : Module.Finite 𝕜 ↥(convCH hom W n 0) :=
    convFiltrationFin 𝕜 (W.C.homology n) (fun t => convCH hom W n t)
      (fun t => convCH_succ_le hom W n t) n (convCH_bot hom W n) hgr
  have hfin : Module.Finite 𝕜 (W.C.homology n) := by
    haveI := hA0
    have htop : Module.Finite 𝕜 ↥(⊤ : Submodule 𝕜 (W.C.homology n)) :=
      Module.Finite.equiv (LinearEquiv.ofEq _ _ (convCH_zero hom W n))
    exact Module.Finite.equiv Submodule.topEquiv
  exact ⟨hfin, (convPage 𝕜 W n hfin).2⟩

end

theorem convFin (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (N : ℕ) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀))
    (hfinB : ∀ s : ℕ, s ≤ N → FiniteDimensional 𝕜 (Work.Pi6.Coh 𝕜 B s))
    (hfinF : ∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜
      (Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))
    (n : ℕ) (hn : n ≤ N) :
    Module.Finite 𝕜 ((Work.Pi6.MSS.serreCF 𝕜 E B p).C.homology n) ∧
      (∑ s ∈ Finset.range (n + 1),
          Module.finrank 𝕜 (Work.Pi6.MSS.pEraw 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) (n + 2) s n))
        = Module.finrank 𝕜 ((Work.Pi6.MSS.serreCF 𝕜 E B p).C.homology n) :=
  convFinAux 𝕜 (serreCF 𝕜 E B p) n
    (fun s hs => e2Fin 𝕜 E B p e₀ N hfib hconn hfinB hfinF s n hs hn)

end Work.Pi6.MSS
