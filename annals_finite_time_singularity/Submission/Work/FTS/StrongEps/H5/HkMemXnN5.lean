import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Range
import Submission.Work.FTS.StrongEps.H5.DataW
import Submission.Work.FTS.StrongEps.H5.Data
import Submission.Work.FTS.StrongEps.H5.LevelShift
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN
import Submission.Work.FTS.StrongEps.H5.Nb5Pkgs
import Submission.Work.FTS.StrongEps.H5.Nb5Core
import Submission.Work.FTS.StrongEps.H5.AtomsW5
import Submission.Work.FTS.StrongEps.H5.HAtoms5
import Submission.Work.FTS.StrongEps.H5.SmoothK5
import Submission.Work.FTS.StrongEps.H5.Atoms.FixedAtoms5
import Submission.Work.FTS.StrongEps.H5.Atoms.SinSqSlot5
import Submission.Work.FTS.StrongEps.H5.AngRad5.AngRadHkMem5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.H5

/-- **The `N`-block at level 5** (the level-`5` analogue of `HkMemXnN`).

The proof is the level-4 `nb_data` proof (in `Submission/Work/FTS/StrongEps/ClassCRHS/HkMemXnNCore.lean`)
carried out one level up: apply the level shift `H5.HkSq_succ_le`
(`HkSq α 5 h ≤ HkSq α 4 h + HkSq α 4 (Dz h) + HkSq α 4 (Dth h)`) to the `NBlk` pieces, use the
Leibniz identities `H5.Dz_mul_eqOn_Q0` / `H5.Dth_mul_eqOn_Q0` to move the extra derivative onto one
factor, and price each of the resulting level-four products by the *proved* level-four rules
(`OpenPkg.prod_field`, `OpenPkg.wprod_field_winf`) through the wrappers `H5.L5_mul` / `H5.W5_mul`.
The extra data needed for each of the twenty pieces is the `L5`/`W5` bundle of its two factors:
the atoms are `Rop/Uop/Vop(PhiTg α w Φg)` (from `EllPkgK α 6`, whose `HQo α 6` data gives the
level-`5` and derivative data by monotonicity), the star coefficients from `StarPkg6 α Cs6 Φs`,
the fixed `F_*`, `DthF_*`, `DzF_*`, `FK F_*`, `hKer` atoms, and `w`, `Dth w`, `Dz w`, `FK w`,
`(z/(1+z))·(w, Dth w, Dz w)`, `(z/(1+z))F_*`-atoms.  The sum-to-`N` transfer of the pieces is the
level-`5` analogue of `ClassCRHS.HkSumOpenClosure` (same proof, `4 → 5`; `HkMem_of_majorant` is
level-general). -/
theorem HkMemXnN5 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B Ce Cs6 : ℝ} {Φs : Work.FTS.Galerkin.Fn},
    ∃ K : ℝ, 0 < K ∧ ∀ {w Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.FTS.VocabO.EllPkgGo α Ce w Φg → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
      Work.Spaces.HkMem α 5 (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)) ∧
      Work.Spaces.HkNorm α 5 (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ)) ≤ K := by
  intro α hαI C₀ B Ce Cs6 Φs
  have hHf : HFixed5Pkg := by
    intro α' hα'I
    obtain ⟨C, hC, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      Atoms.FixedAtoms5 Work.FTS.StrongEps.H5.AngRad5.AngRadHkMem5 α' hα'I
    exact ⟨C, hC, ⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, ⟨h7, h8⟩, ⟨h9, h10⟩⟩
  obtain ⟨K, hK, hmain⟩ :=
    HkMemXnN5_of_atoms Atoms.HAtoms5 Atoms.WAtomsStar5 Atoms.WAtomsFixed5 hHf
      Atoms.SinSqSlot5
      (fun {α} hαI {Ce Cs6} {Φs w Φg} hw hell hstar k hk =>
        NBlk_smoothK (w := w) (Φs := Φs) (Φg := Φg) hαI.1 hαI.2 hw hell hstar k hk)
      (fun {α} hαI {Ce Cs6} {Φs w Φg} hw hell hstar =>
        SmoothOpenN_K (Φs := Φs) (w := w) (Φg := Φg) hαI.1 hαI.2 hw hell hstar)
      hαI (C₀ := C₀) (B := B) (Ce := Ce) (Cs6 := Cs6) (Φs := Φs)
  exact ⟨K, hK, fun hw hXw hX6 _hgo hell hstar => hmain hw hXw hX6 hell hstar⟩

end Work.FTS.StrongEps.H5
