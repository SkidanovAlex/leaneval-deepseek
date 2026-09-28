import Mathlib
import Submission.Work.Serre.MapPathDefs
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.mpathQ_isSerreFibration
import Submission.Work.Serre.mpathFst_ratHomologyIso
import Submission.Work.Serre.mpathQ_fibreHomeo

namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- Step A of the proof of `Work.Serre.SerreE3a`: the honest-fibre form implies the homotopy-fibre form, by the mapping path space construction.

For `p : E → B` and `e₀`, let `E''` be `{x : E × C(I,B) // x.2 0 = p x.1}` (a subtype of the product,
with the subspace topology) and let `q : E'' → B` send `(e,γ)` to `γ 1`.  Then `q` is a Serre
fibration (it is `ev₁` composed with the pullback of `ev₀` along `p`), the projection `r : E'' → E`
is a homotopy equivalence (homotopy inverse `e ↦ (e, const (p e))`, via the contraction
`γ ↦ (s ↦ γ (t·s))`), `p ∘ r` is homotopic to `q` (through `(e,γ) ↦ γ t`), and the fibre of `q`
over `b₀` is homeomorphic to `Work.RatHurewicz.homotopyFibre p e₀` by path reversal
(`γ ↦ γ.symm`).  So the acyclicity hypothesis on the homotopy fibre transfers to `q`, and
`SerreE3aFibreAcyclic` at `q` gives the conclusion, transported back along `r`.

The two descriptions of the homotopy fibre (`Work.RatHurewicz.homotopyFibre p e₀`, whose paths run
from `p e₀` to `p e`, and the fibre of `q`, whose paths run from `p e` to `b₀ = p e₀`) differ by
reversal: use `Path.symm`. -/
theorem serreE3aStepA : Work.Serre.SerreE3aFibreAcyclic → Work.Serre.SerreE3a := by
  intro hA E B _ _ p e₀ N _hp hB hacyc i hi
  -- `q = mpathQ p` is a Serre fibration with the same homotopy fibre
  have hq : Work.StemsB.IsSerreFibration (mpathQ p) := mpathQ_isSerreFibration p
  -- its honest fibre over `p e₀` is `homotopyFibre p e₀`, so it is acyclic below `N`
  have hfib : ∀ t : ℕ, 0 < t → t ≤ N →
      IsZero (ratH (TopCat.of (Work.StemsB.fibre (mpathQ p) (p e₀))) t) := by
    intro t ht htN
    obtain ⟨e⟩ := mpathQ_fibreHomeo p e₀
    haveI : IsIso (ratHomologyMap (e.toHomotopyEquiv.toFun) t) :=
      IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv t
    exact IsZero.of_iso (hacyc.1 t ht htN) (asIso (ratHomologyMap (e.toHomotopyEquiv.toFun) t))
  -- and `H₀` of that fibre is `ℚ`
  have h0 : Nonempty (ratH (TopCat.of (Work.StemsB.fibre (mpathQ p) (p e₀))) 0
      ≅ ModuleCat.of ℚ ℚ) := by
    obtain ⟨e⟩ := mpathQ_fibreHomeo p e₀
    haveI : IsIso (ratHomologyMap (e.toHomotopyEquiv.toFun) 0) :=
      IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv 0
    haveI : IsIso (ratHomologyMap (toPoint (Work.RatHurewicz.homotopyFibre p e₀)) 0) := hacyc.2
    refine ⟨(asIso (ratHomologyMap (e.toHomotopyEquiv.toFun) 0)).trans ?_⟩
    exact (asIso (ratHomologyMap (toPoint (Work.RatHurewicz.homotopyFibre p e₀)) 0)).trans
      (ratH_zero_of_pathConnected PUnit).some
  have hqi : IsIso (ratHomologyMap (mpathQ p) i) :=
    hA (mpath p) B (mpathQ p) (p e₀) N hq hB hfib h0 i hi
  -- `p ∘ mpathFst p ~ mpathQ p`, and `mpathFst p` is a rational homology isomorphism
  have hfst : IsIso (ratHomologyMap (mpathFst p) i) := mpathFst_ratHomologyIso p i
  have hhom : (p.comp (mpathFst p)).Homotopic (mpathQ p) := mpath_homotopic p
  have hcomp : ratHomologyMap (p.comp (mpathFst p)) i
      = ratHomologyMap (mpathFst p) i ≫ ratHomologyMap p i :=
    ratHomologyMap_comp (mpathFst p) p i
  have heq : ratHomologyMap (p.comp (mpathFst p)) i = ratHomologyMap (mpathQ p) i :=
    ratHomologyMap_eq_of_homotopic hhom.some i
  haveI := hfst
  have h2 : IsIso (ratHomologyMap (mpathFst p) i ≫ ratHomologyMap p i) := by
    rw [← hcomp, heq]; exact hqi
  exact IsIso.of_isIso_comp_left (ratHomologyMap (mpathFst p) i) (ratHomologyMap p i)

end

end Work.Serre
