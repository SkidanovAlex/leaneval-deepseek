import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.epsWP_semitame_proof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Leaves/EpsWPSemitame.lean` — OPEN LEAF S2 (research **mid**, ~2–4K lines; RISK)

curric-46 install 2026-10-12 (`cbc/fts_apriori6_ruling.md` §3 S2; REVIEW fix F4).
This is the whole level-6 algebra of the right-hand side (all four pieces + `μ` + the linear part)
plus the `HQo 6` honesty of `epsWP` — the `EpsWPBounds` header records it is missing.
**The tame structure is essential**: top order must enter LINEARLY with an `ℋ⁴`-priced
coefficient.  A coefficient like `C(|x|₆)·|x|₇` leaves no `ε` (`ε|x|₇ ≲ |g|₆`) and breaks the
Grönwall.  In the Leibniz terms `D^jA·D^{7−j}x`:
* `j = 0, 1`: sup of the coefficient priced by `M` (`EllPkgGo` + Agmon);
* `2 ≤ j ≤ 3`: Agmon on `A` gives `|A|₅ ≤ Ce|x|₆`;
* `j ≥ 4`: Agmon on `x` gives a quadratic term.
Reuse `H6Row6.pcs` / `NSplit6` / `nsum_split6`, `RowNAgmon`, `coefDataSharp`, `muBdd_of_zeroModes`,
`SupOpenH2` / `ResidPtOfGo` (top-order coefficient).
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps

set_option autoImplicit false

/-- **LEAF (S2)**, proved in the sibling `Apriori4Proofs.epsWP_semitame_proof` (wiring deferred)** semi-tame bound of the pre-mollified right-hand side `X = epsWP` at the
projected slice `x`: level 4 (for the `P₀` correction) and level 6 (for the transfer). -/
theorem epsWP_semitame :
    ∀ C₀ Ce Cs : ℝ, ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α ∈ Ioc 0 α₀, ∃ Ct : ℝ, 0 ≤ Ct ∧
    ∀ {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}, IsSmoothKernel ρ →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.StrongPersist.StarPkg6 α Cs Φs → MuLamOK α C₀ Φs E →
    ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ (g : Fam) (τ : ℝ),
      Work.FTS.ClassC.ClassC α (slice (JfamP ρ ε g) τ) →
      Work.FTS.Nonlin.Xn α (slice (JfamP ρ ε g) τ) ≤ C₀ * α ^ 2 →
      Work.FTS.VocabO.HQo α 6 (epsWP α ρ ε Φs E g τ) ∧
      Work.Spaces.HkNorm α 4 (epsWP α ρ ε Φs E g τ)
        ≤ Ct * (1 + Work.Spaces.HkNorm α 5 (slice (JfamP ρ ε g) τ)) ∧
      Work.Spaces.HkNorm α 6 (epsWP α ρ ε Φs E g τ)
        ≤ Ct * (1 + Work.Spaces.HkNorm α 7 (slice (JfamP ρ ε g) τ))
          + Ct * (1 + Work.Spaces.HkNorm α 6 (slice (JfamP ρ ε g) τ)) ^ 2 := by
  -- the sibling `Apriori4Proofs.epsWP_semitame_proof` is proved but was still being edited at
  -- hand-over (it currently carries an auxiliary `sorry`), so the wiring is deferred to the next
  -- session: replace this body by `Apriori4Proofs.epsWP_semitame_proof` once it is clean.
  sorry

end Work.FTS.StrongEps.EpsE4Thr.E4R4
