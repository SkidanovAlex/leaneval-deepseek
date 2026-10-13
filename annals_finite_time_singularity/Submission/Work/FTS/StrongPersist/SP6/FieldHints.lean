/-
# `FTS/StrongPersist/SP6/FieldHints.lean` — the route for the five `FlatW 6` field bounds

This module exists to carry the **route** for the five per-field lemmas

* `Work.FTS.StrongPersist.SP6.FieldEH`
* `Work.FTS.StrongPersist.SP6.FieldEVz`
* `Work.FTS.StrongPersist.SP6.FieldEV`
* `Work.FTS.StrongPersist.SP6.FieldEUz`
* `Work.FTS.StrongPersist.SP6.FieldEU`

(each: `∃ C > 0, ∀ α K KY KD Y, 0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → SmoothOpen Y → FlatW 7 Y K →
Fb 6 KY Y → F0 6 KD (Yblk Y) → FlatW 6 (field) (C·(α+1)·(K+KY+KD))`), by listing the
already-proved ingredients and the skeleton.  Nothing here is needed for the proofs; it is
documentation with an importable name.

## The five fields (`PhiStar/CoreAux/FieldsDefs.lean`)

```
Yblk Y = fun z θ => z * pz Y z θ                       -- D_z Y
Tblk Y = fun z θ => s2 θ * pth Y z θ = D_θ Y           -- s2 θ = sin 2θ
Wone α Y = fun z θ => 3 * Y z θ + α * (Y z θ / (z+1) + Yblk Y z θ)
EH  α Y  = fun z θ => 2*Y + 2*α*sin²θ*(Y/(z+1) + Yblk Y) + Tblk Y
EVz Y    = fun z θ => 2*(cos²θ - 2 sin²θ)*Y + Tblk Y
EV  Y    = fun z θ => z/(z+1) * EVz Y
EUz α Y  = -Wone α Y
EU  α Y  = -(z/(z+1)) * Wone α Y
```

## What `FlatW 6 f K` means (`VocabO2.FlatW`)

`(∀ k ≤ 6, |(z+1)^k pzIter k f| ≤ K) ∧ (∀ k i, k+i+1 ≤ 6, |(z+1)^k pzIter k (DthIter i (pth f))| ≤ K)`
on the open quadrant `Q0 = (0,∞) × (0,π/2)`.  Equivalently (`FTS/StrongPersist/StarPkg6Aux.lean`):

* `flatW6_of_F0 h1 h2 : FlatW 6 f K` from `h1 : F0 6 K f` and `h2 : F0 5 K (pth f)`
  (the radial clause is the `i = 0` slot of `F0 6`, the angular clause is exactly `F0 5 ∘ ∂_θ`).

## Ingredients already proved (import them)

**Flat-calculus helpers** (`FTS/StrongPersist/StarPkg6Aux.lean`):

* `smoothOpen_theta_only`, `smoothOpen_z_only`, `smoothOpen_add`, `smoothOpen_neg`,
  `smoothOpen_const`, `smoothOpen_const_mul` — smoothness of the coefficient functions;
* `pth_theta_only` (`∂_θ` of a `θ`-only function is its `ℝ`-derivative), `pth_z_only`,
  `pth_const`;
* `F0_Dth_shift : F0 (n+1) K g → F0 n K (Dth g)`;
* `F0_zero`, `F0_const_mul : F0 n K f → SmoothOpen f → F0 n (2^n·|c|·K) (c·f)`,
  `Fb_const_mul : Fb n K f → SmoothOpen f → Fb n (2^{n+1}·K·|c|) (c·f)`;
* `Fb_congr_Q0`, `FlatW_mono`, `flatW6_of_F0`.

**Coefficient calculus** (`FTS/StrongPersist/StarPkg6Fields.lean`, namespace
`Work.FTS.StrongPersist`):

* `deriv_sin_sq`, `deriv_cos_sq_sub_two_sin_sq`, `deriv_sin_two`, `deriv_cos_two` — the four
  `ℝ`-derivative identities of the angular coefficients;
* the absorption lemmas `mono3_le_big`, `mono_le_unit`, `mono_le_unit_alpha`,
  `eight_unit_le`: **all constants are finally compared by writing the field constant as a sum
  of monomials `2^j·u·v·w·M^c·({1,α})·S` (with `u,v,w ∈ {Ac,Az,1}`, `u,v,w ≤ M`,
  `j ≤ 45`, `c ≤ 37`, `M = Ac+Az+1 ≥ 1`, `S = K+KY+KD ≥ 0`) and applying these lemmas**;
  `C = 2^48·(Ac+Az+1)^40 + 8` dominates the sum of at most seven such monomials.

**CoreAux** (`FTS/PhiStar/CoreAux/`):

* `F0_mul`, `F0_add`, `F0_zpz` (`F0 (n+1) K f → F0 n ((n+1)K) (z·∂_z f)`), `F0_congr`,
  `Fbq_F0_congr`, `Fbq_pzIter_congr`, `Fbq_DthIter_congr`, `Fbq_pth_mul`;
* `Fb_add`, `Fb_mul_theta_free` (`Fb n K f → F0 n A c → F0 n A (pth c) → Fb n (2^{n+1}·K·A)
  (fun z θ => f z θ * c z θ)` — valid for **any** `c`, not only `z`-free ones),
  `Fb.of_both`;
* `F0_theta_coefs 6` (one `Ac > 0` with `F0 6 Ac` of `sin²θ`, `cos²θ-2sin²θ`, `cos2θ`, `sin2θ`)
  and `F0_z_coefs 6` (one `Az > 0` with `F0 6 Az` of `z/(1+z)` and `(1+z)⁻¹`);
* `smoothOpen_inv_one_plus_z_fts`, `smoothOpen_z_div_one_plus_z_fts` (`Fb_EU_bound.lean`),
  `Fbq_smoothOpen_mul`, `pth_zpz_smoothOpen`, `DthIter_Dz_comm_smoothOpen`;
* `F0_z_coefs`-based `F0_congr` transfers.  The four `F0 5`/`F0 6` facts of the *derivatives* of
  the angular coefficients follow from the four identities above plus `F0_const_mul`.

## The skeleton (see `NOTES_EH_wip.lean.txt` for a worked, if unfinished, instance)

1. obtain `Ac`, `Az` from the two coefficient bundles, set `M := Ac+Az+1`, `S := K+KY+KD`,
   and the master piece constant `B := 2^12·M^2·S`;
2. prove the **blocks** `F0 6 B` and `Fb 5 B` of `Y`, `Yblk Y`, `Tblk Y`, `Y·(1+z)⁻¹`
   (using `F0_zpz` at order 6 for `Yblk`, `pth_zpz_smoothOpen` + `F0_zpz` for `pth (Yblk Y)`,
   `F0_mul` for `Tblk Y`, `F0_Dth_shift` for `Dth (pth Y)` inside `pth (Tblk Y)`, `F0_mul`
   for `pth (Y·(1+z)⁻¹)`);
3. build the field: `F0 6` by `F0_mul`/`F0_add`/`F0_const_mul` on the blocks, and the
   `∂_θ`-clause by `Fb 5` (`Fb_add`, `Fb_mul_theta_free`, `Fb_const_mul`), then
   `flatW6_of_F0` on the two components (raised to the sum of the two constants by `F0.mono`);
4. compare the resulting constant with `(2^48·M^40 + 8)·(α+1)·S` by expanding it with `ring`
   into a sum of monomials and applying the absorption lemmas (`mono_le_unit`,
   `mono_le_unit_alpha`) and `eight_unit_le`.

**Pricing warning.**  `EUz α Y` and `EU α Y` (and `EH α Y`) grow **linearly in `α`**, so their
constants must carry the factor `(α+1)`; the statement above carries it for all five fields
(for the `α`-free `EVz`, `EV` this is only a weakening).  Without the `(α+1)` on `EU` the
statement is *false* (see `SP6/FlatW6Fields.lean`, `not_FlatW6Fields`).
-/
import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.StrongPersist.StarPkg6Aux
import Submission.Work.FTS.StrongPersist.StarPkg6Fields
import Submission.Work.FTS.PhiStar.CoreAux.FieldsDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

/-- A placeholder carrying the route; it says nothing. -/
theorem FieldHints_trivial : (0 : ℝ) = 0 := rfl

end Work.FTS.StrongPersist.SP6
