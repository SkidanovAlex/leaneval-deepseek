import Mathlib
import Submission.Work.SSGRoute.ExtChain.subsingleton_ext_fpRegular
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Coefficient modules for the degree-two dévissage in the first variable

Fix a prime `p` and a group `H`.  We record the two building blocks of the `𝔽_p[H]`-module
structure theory used in `Work.ExtChain.ext2_fn_ptorsion_of_trivial`:

* `trivPow p H a` — the **trivial** `𝔽_p[H]`-module of `𝔽_p`-rank `a`, i.e. `𝔽_p^a` with `H`
  acting trivially (written as the `𝔽_p`-module `Fin a →₀ 𝔽_p`);
* `regPow p H b` — the **free (regular)** `𝔽_p[H]`-module of rank `b`, i.e. `𝔽_p[H]^b` (written as
  the `𝔽_p[H]`-module `Fin b →₀ 𝔽_p[H]`).

Both are objects of `Rep.{0} Coeff H` with `Coeff = ULift ℤ`; this is the ambient category in which
the Hasse-principle dévissage takes place.

The companion results are

* `Work.ExtChain.ptorsion_two_decomp` (`p = 2`): a finite `2`-torsion `𝔽₂[H]`-module is a direct
  sum of copies of `trivPow 2 H a` and `regPow 2 H b`;
* `Work.ExtChain.ptorsion_odd_retract` (`p ≠ 2`): a finite `p`-torsion `𝔽_p[H]`-module is a
  retract of `regPow p H b`.

With `H` of order two, `Work.SSGRoute.ExtChain.subsingleton_ext_fpRegular` kills the `Ext^{≥2}` of
the regular block, so in both cases `Ext²_H(N,·)` is controlled by `Ext²_H(𝔽_p,·)`.
-/

namespace Work.ExtChain

noncomputable section

/-- The trivial `𝔽_p[H]`-module of `𝔽_p`-rank `a`, as an object of `Rep Coeff H`. -/
def trivPow (p : ℕ) (H : Type) [Group H] (a : ℕ) : Rep.{0} SSGRoute.PTExt.Coeff H :=
  Rep.trivial SSGRoute.PTExt.Coeff H (Fin a →₀ ZMod p)

/-- The free (regular) `𝔽_p[H]`-module of rank `b`, as an object of `Rep Coeff H`. -/
def regPow (p : ℕ) (H : Type) [Group H] (b : ℕ) : Rep.{0} SSGRoute.PTExt.Coeff H :=
  Rep.ofDistribMulAction SSGRoute.PTExt.Coeff H (Fin b →₀ MonoidAlgebra (ZMod p) H)

/-- The trivial `𝔽_p[H]`-module of rank one, as an object of `Rep Coeff H`. -/
def trivOne (p : ℕ) (H : Type) [Group H] : Rep.{0} SSGRoute.PTExt.Coeff H :=
  Rep.trivial SSGRoute.PTExt.Coeff H (ZMod p)

/-- The regular `𝔽_p[H]`-module (free of rank one), as an object of `Rep Coeff H`. -/
def regOne (p : ℕ) (H : Type) [Group H] : Rep.{0} SSGRoute.PTExt.Coeff H :=
  SSGRoute.PTExt.modRep H (MonoidAlgebra (ZMod p) H)

end

end Work.ExtChain
