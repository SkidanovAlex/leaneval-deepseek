/-
# ZeroFreeTables — HBLemma10_3_engine_proof

Proof of the §10 engine `Work.ZeroFreeTables.HBLemma10_3_engine` (HB (10.14) in its
setting, the inequality that refutes `λ₃ ≤ 6/7`).

## RESOLVED: class `mu_2 + mu_3` too -- the gap was a missing row in the table

Re-reading HB's (10.3) settles it.  His `Sigma_2` is
`sum_{j<k} { K(beta + i(gam_j + gam_k), chi_j*chi_k) + K(beta + i(gam_j - gam_k), chi_j*chi_k) }`
-- the *same* character `chi_j*chi_k` at the *two* points `+-(gam_j -+ gam_k)`.  In case 3 all
characters are real, so `chi_j*chi_k^{-1} = chi_j*chi_k` and this agrees with the plain expansion
`z_j*z_k` and `z_j*zbar_k`; either way the pair monomials are `(1,1,0)`-type and `(1,-1,0)`-type.
My table listed only the `(1,1,0)`-type rows, which is why `E_2`, `E_3` appeared to be missing at
the shift `mu_2 + mu_3`.  The complete accounting (all rows, with conjugates, using that
`chi_1^{-1}*chi_3 = chi_2`, `chi_1*chi_2^{-1} = chi_3`, etc. because all are real):

| monomial | exponent | character | extraction | argument shift |
|---|---|---|---|---|
| `(1,-1,0)` | `-gam_2` | `chi_3` | `E_3` | `-mu_2 - mu_3` (class 3, evenness) |
| `(1,0,-1)` | `-gam_3` | `chi_2` | `E_2` | `-mu_2 - mu_3` (class 3, evenness) |
| `(0,1,1)` | `gam_2+gam_3` | `chi_1` | `E_1` | `mu_2 + mu_3` (class 3) |
| `(-1,1,0)` | `gam_2` | `chi_3` | `E_3` | `mu_2 - mu_3` (class 2) |
| `(-1,0,1)` | `gam_3` | `chi_2` | `E_2` | `mu_3 - mu_2` (class 2, evenness) |
| `(0,1,-1)` | `gam_2-gam_3` | `chi_1` | `E_1` | `mu_2 - mu_3` (class 2) |

Each of these has weight `1/4`, and each pairs with its conjugate monomial (`a -> -a`) of weight
`1/4`, which gives the *same* functional (real characters) and the *same* argument shift
(evenness).  So every extraction enters **both** the class-2 and the class-3 shift with weight
`1/2`, and the principal poles likewise enter each class with weight `1/2`.  Hence

  `raw shifted part = (1/2)*P*(mu_2 + mu_3) + (1/2)*P*(mu_2 - mu_3)`  -- exactly,

with no gap.  Together with the shift-`0` class (weight `1`, giving `P*(0)`, the first four terms
of (10.13)) this *is* HB's (10.13):

  `raw = P*(0) + (1/2)*(P*(mu_2+mu_3) + P*(mu_2-mu_3)) + (the eps-terms)`.

So the plain three-factor expansion *does* imply (10.13), via the (10.3) pairing; and with
`P*(t) <= 0` (`P10.P3star_nonpos`, side condition `a^{-3} <= sum (a+lam_j)^{-3}`) the three
`P*`-blocks are non-positive slack and drop out, leaving (10.14) with the budget `3/4 + eps`.
The weights are therefore pinned: **classes `0`, `mu_2+mu_3`, `mu_2-mu_3` with weights
`1`, `1/2`, `1/2`**, and the two bookkeeping facts recorded above (evenness; the `phi/2 = 1/8`
constants landing the residual at `3/8`) are all that the five-`P*` assembly needs.

## The three-class decomposition (case 3, `gam_1 = 0`): two classes match (10.13) exactly

Writing `Pi(t) = Re P3(alpha/(a+it))` and `E_j(t) = Re P3(alpha/(a+lam_j+it))`, so that
`P*(t) = Pi(t) - E_1(t) - E_2(t) - E_3(t)`, and collecting the monomials of the table by their
*argument shift* (using that all characters of case 3 are real, so the functionals and the
quantities `Pi`, `E_j` are even in the shift) gives:

* **argument shift `0`** (weight `1`): monomials `(0,0,0)` [`Pi`], `(+-1,0,0)` [`E_1`, total
  weight `1`], `(0,+-1,0)` [the `chi_2`-functional at `sigma +- i gam_2`, whose extraction of
  `rho_2` has argument shift `gam_2 - gam_2 = 0`, weight `1`], `(0,0,+-1)` [same for `rho_3`,
  weight `1`].  Total: `P*(0)` with weight `1` -- and `P*(0)` *is* the first four terms of
  (10.13), since `E_1(0) = Re P3(alpha/(a+lam_1)) = P3R 1` and `Pi(0) = P3R (alpha/a)`;
* **argument shift `mu_2 - mu_3`** (weight `1/2`): the principal monomials `(+-1,1,-1)` and
  conjugates give `Pi` with weight `1/2`; the pairs `(1,1,0)` [`E_3`], `(-1,0,1)` [`E_2`] and
  `(0,+-1,-1)` [`E_1`] each give weight `1/2`.  Total: exactly `(1/2)*P*(mu_2 - mu_3)`;
* **argument shift `mu_2 + mu_3`** (weight `1/2`): the principal monomials `(+-1,1,1)` and
  conjugates give `Pi` with weight `1/2`, and `(0,+-1,1)` gives `E_1` with weight `1/2` -- but
  **no monomial supplies `E_2` or `E_3` at this shift**.  The collected value is therefore
  `(1/2)*(Pi - E_1)(mu_2+mu_3)`, whereas (10.13) carries `(1/2)*P*(mu_2+mu_3)`.

So (10.13) agrees *exactly* with the collected bound in the first two classes and is larger in
the third by `(1/2)*(E_2 + E_3)(mu_2+mu_3) >= 0`.  Consequently the combination's bound does
**not** by itself imply (10.13): some further terms of HB's combination must supply `E_2`, `E_3`
at the shift `mu_2 + mu_3` (equivalently, at the exponent `gam_2 + gam_3` there must be
`chi_2`/`chi_3`-functionals that the raw expansion of `prod(1+Re z_j)` does not contain -- the
points `sigma +- i(gam_j +- gam_k)` used in (10.2)-(10.3) must be paired differently, or HB's
combination for the case `chi_1*chi_2*chi_3 = chi_0` is not the plain three-factor expansion
but the (9.1)-style one).  This is the precise question that remains; it is now localised to a
single class.

## The assembly: raw weights are HALF the `P*` weights, and the dropped extractions matter

Working the balance out of the table (case 3, `gam_1 = 0`) exposed a further point that must be
pinned before the five-`P*` assembly is stated:

* at the shift `t = mu_2 + mu_3` the raw terms are the pole (weight `1/4`: the two principal
  triples `a_1 = +-1`) *and* the `rho_1`-extraction (weight `1/4`: the monomial `(0,1,1)`).
  The `rho_2`/`rho_3` extractions are **not supplied at that exponent at all** -- no monomial has
  character `chi_2` or `chi_3` at the exponent `gam_2 + gam_3` (see the table);
* so the raw contribution there is `(1/4)*[Re P3(alpha/(a+it)) - Re P3(alpha/(a+lam_1+it))]`,
  i.e. a *truncated* `P*`, not a full one.  Comparing with `(1/2)*P*(t)` (whose pole weight is
  `1/2`, and which subtracts all three extractions):
  `(1/2)*P*(t) - raw = (1/4)*pole - (1/2)*(extr_2 + extr_3) + (1/4)*extr_1`;
* hence `raw <= (1/2)*P*(t)` is **not** automatic: it needs the dropped extractions
  `extr_2, extr_3` to be large enough.  They are `>= 0` by the dropping rule
  (`Re P3(alpha/(a+lam_j+it)) >= 0`, i.e. `lam_1 <= lam_j`), which gives the *other* direction,
  so the sign has to be handled explicitly rather than by monotonicity in the weights;
* at the `gam_2`/`gam_3` classes the situation is dual: the extraction weights are `1/4` while
  the pole weights there are `1/8`.

Consequence: the assembly's statement must be written with the weights *and* the sign of the
dropped extractions pinned -- exactly the family of error review has caught twice already
(the `3/4` coefficient, and the `24/(delta*L)` charge).  Do not state it from the table alone;
pin this first.

## The monomial table for case 3 (`gam_1 = 0`)

From `three_char_combination`, the monomials `prod z_j^{a_j}` (`a_j in {0,+-1}`) of
`prod (1 + Re z_j)` have coefficients `1/2` (one index), `1/4` (two) and `1/8` (three), and the
constant has `1`.  With `gam_1 = 0` the (character, exponent) pairs are:

| `a` | character | exponent | what it supplies |
|---|---|---|---|
| `(0,0,0)` | `1` | `0` | the pole term at the base point |
| `(+-1,0,0)` | `chi_1` (real) | `0` | extraction of `rho_1`, argument-shift `0` |
| `(0,1,0)`/`(0,-1,0)` | `chi_2` (real) | `+-gam_2` | extraction of `rho_2`, shift `0` |
| `(0,0,+-1)` | `chi_3` (real) | `+-gam_3` | extraction of `rho_3`, shift `0` |
| `(1,1,0)` | `chi_3` | `gam_2` | extraction of `rho_3`, shift `mu_2 - mu_3` |
| `(-1,0,1)` | `chi_2` | `gam_3` | extraction of `rho_2`, shift `mu_3 - mu_2` |
| `(0,+-1,1)` | `chi_1` | `+-gam_2 + gam_3` | extraction of `rho_1`, shift `mu_2 +- mu_3` |
| `(0,+-1,-1)` | `chi_1` | `+-gam_2 - gam_3` | extraction of `rho_1`, shift `mu_2 +- mu_3` |
| `(+-1,1,1)` | `1` | `gam_2 + gam_3` | pole at shift `mu_2 + mu_3` |
| `(+-1,1,-1)` | `1` | `gam_2 - gam_3` | pole at shift `mu_2 - mu_3` |

Two bookkeeping facts this table makes visible, both needed by the assembly:

* the poles at a given shift come in *pairs* (`a_1 = +-1`), total weight `1/8 + 1/8 = 1/4`, whereas
  the matching extraction of `rho_1` at that shift has weight `1/8` from one monomial and `1/8`
  from its `a_1 = -1` partner *at the conjugate exponent*: so the weights must be matched using
  the evenness of `Re P3(alpha/(a+-it))` and of the exponent pairing, not asserted shift by shift;
* the extraction weights at the `gam_2`/`gam_3` classes are `1/4` against the pole weights `1/8`
  there, so `P*` is entered at the *weighted* combination and `P10.P3star_nonpos` is applied to
  the *difference* form in which the weights balance;  it is in exactly this step that the
  `phi/2 = 1/8` constants must enter so that the residual costs only `3/8` of error.

This table is the reusable core; the assembly of the five `P*` expressions into the single lump
`hPstar` is a separate (delegable) piece, and it should be written only with this table in hand.

## The `mu_2 +- mu_3` matching: first shift class worked out

The pivot is a hypothesis already in the statement: case 3 has `rho_1.im = 0`, so **`gam_1 = 0`,
`mu_1 = 0`**.  (This is why HB's written shifts `mu_2 +- mu_3` look like they use only two of the
three zeros.)  With `gam_1 = 0`, the raw exponents of `Ksum_positivity_three` collapse to
`{0, +-gam_2, +-gam_3, +-gam_2 +- gam_3}`, and the monomials `z_1^a1 z_2^a2 z_3^a3` of the
pointwise expansion to:

* exponent `gam_2` (`a = (1,1,0)`, character `chi_1*chi_2 = chi_3`): the term HB quotes,
  `chi_1(n)*chi_2(n)*n^{-i gam_2}`; its extraction of `rho_3` has argument
  `(a+lam_3) + i*(gam_2 - gam_3)*L = (a+lam_3) + i*(mu_2 - mu_3)` -- i.e. it lands in
  `P*(mu_2 - mu_3)`;
* exponent `gam_3` (`a = (-1,0,1)`, character `chi_1^{-1}*chi_3 = chi_2`): its extraction of
  `rho_2` is `(a+lam_2) + i*(mu_3 - mu_2)`, which is in `P*(mu_2 - mu_3)` **because `P*` is even
  in `t`** (`Re P3(alpha/(a-it)) = Re P3(alpha/(a+it))`, `P3` having real coefficients);
* exponent `gam_2 + gam_3` (`a = (0,1,1)`, character `chi_2*chi_3 = chi_1`): extraction of `rho_1`
  in `P*(mu_2 + mu_3)`; and `a = (1,1,1)` (principal) at the same exponent gives the *pole* term
  `Re P3(alpha/(a+i*(mu_2+mu_3)))` that heads `P*(mu_2 + mu_3)`;
* exponent `gam_2 - gam_3` (character `chi_1`, and principal): same, in `P*(mu_2 - mu_3)`.

Direction to use: (10.13) needs `(1/2)*(P*(mu_2+mu_3) + P*(mu_2-mu_3))` as a **bound**, not an
equality -- `P*(t) <= 0` is all that is consumed, so extractions that a given exponent does not
supply (e.g. `lam_2`, `lam_3` at the shift `mu_2+mu_3`) are simply *dropped* from the `P*`
expression, which only makes it larger, and each surviving `P*(t)` is closed by
`P10.P3star_nonpos` under `1/a^3 <= sum 1/(a+lam_j)^3`.  The pair errors cost
`6*(1/2)*8*alpha/(delta*L)` and the `phi/2`'s `6*(1/2)*(1/8) = 3/8`, i.e. the `alpha*(3/8+eS)`.

Remaining for the provider: the last two exponent classes (`+-gam_2 +- gam_3` with the
`chi_1`/principal characters) and the bookkeeping that assembles the five `P*`-expressions into
the single lump `hPstar`; then the errors.

## The `hPstar` provider: structure pinned, one sub-question left

Structure (all ingredients proved or delegated):

* the four *shifted principal* bounds: `SigmaP3L N L 1 (sigma + i*tau) <= Re P3(alpha/((s-1)L)) + alpha*(0+e)`,
  obtained from `P9.zetaEngine_principal_proof` and identified with `P3R`'s shifted form by
  `P3_pole_shift_eq`;
* the six *shifted pair* bounds: `P10.shifted_extract_of_point_bound` (proved): for a pair
  functional `chi_j*chi_k^{+-1}` at `sigma + i*tau`,
  `SigmaP3L <= -Re P3(alpha/((a+lam_l) + i*(tau - gam_l)*L)) + 8*alpha/(delta*L) + alpha*(c+e)`;
* the collapse identities `char_prod_pair_eq_third`, `char_signed_triples_eq_one`;
* the closure `P10.P3star_nonpos` under the side condition `1/a^3 <= sum 1/(a+lam_j)^3`;
* the arithmetic: the six pair errors cost `6*(1/2)*(8*alpha/(delta*L)) = 24*alpha/(delta*L)`
  and `6*(1/2)*(1/8) = 3/8`, giving `alpha*(3/8 + eS)`.

**Left to settle (do not guess)**: (10.13) presents the shifted part at the *two* shifts
`mu_2 +- mu_3`, while the raw shifted terms of `Ksum_positivity_three` sit at the ten shifts
`+-gam_j +- gam_k` (pairs) and `+-gam_1 +- gam_2 +- gam_3` (triples).  HB's remark identifies one
such term via `chi_1(n)*chi_2(n)*n^{-i gam_2} = chi_3(n)*n^{-i gam_2}`, i.e. a *specific* example;
the general matching must come from the collapse `chi_j*chi_k = chi_l` turning raw terms with
different characters *and* different points into the same functional.  Before writing the
provider, work out that matching explicitly (which raw pair/triple term contributes to which
`P*(mu_2 +- mu_3)` argument) from HB §10 in `dev/hb.txt`; the statement of the provider should be
written only once that matching is fixed.

## SETTLED against HB (10.13): the shift alignment of the `P*` residual

HB's own text (`dev/hb.txt`, the case `chi_1*chi_2*chi_3 = chi_0` with real `chi_j`, `rho_1`
real) reads: with `s = 1 + a/L`,

  `P3((a+lam_1)/a) - P3(1) - P3((a+lam_1)/(a+lam_2)) - P3((a+lam_1)/(a+lam_3))`
  `+ (1/2)*{P*(mu_2+mu_3) + P*(mu_2-mu_3)} + (a+lam_1)*(6*phi/2 + eps) >= 0`     (10.13)

with `phi = 1/4` and

  `P*(t) = Re{P3((a+lam_1)/(a+it)) - P3((a+lam_1)/(a+lam_1+it)) - P3((a+lam_1)/(a+lam_2+it)) - P3((a+lam_1)/(a+lam_3+it))}`,

and the paper's remark identifies the terms via `chi_1(n)*chi_2(n)*n^{-i gam_2} = chi_3(n)*n^{-i gam_2}`.

Three consequences, all now pinned:

* **the coefficient is confirmed**: `6*phi/2 = 3/4` at `phi = 1/4`, so the budget of the bridge
  is exactly the `3/4 + eps` of `case3_weighted_combination` and of `p1014_of_extractions`;
* **the unshifted terms of (10.13) are exactly the three extractions** `P3(1)` (i.e.
  `P3(alpha/(a+lam_1))`), `P3(alpha/(a+lam_2))`, `P3(alpha/(a+lam_3))` -- the shape
  `extraction_of_weighted_sum` consumes, so the unshifted half of the interface is right;
* **the shifted part is `(1/2)*(P*(mu_2+mu_3) + P*(mu_2-mu_3))`, i.e. two shifts and `P*` at a
  *common* shift** -- whereas the raw combination's shifted terms (the six pairs at
  `sigma + i*(+-gam_j +- gam_k)` and the four triples at `sigma + i*(+-gam_1 +- gam_2 +- gam_3)`,
  which `hPstar` reproduces verbatim) carry shifts `(gam_j +- gam_k) - gam_l` in their
  extractions.  So the *provider* of `hPstar` must first perform HB's collapse rewrite
  (pair/triple identifications at a common exponent) to bring the shifted part into the
  `P*(mu_2+-mu_3)` form, and only then close each `P* <= 0` by `P10.P3star_nonpos` and collect
  the errors into `alpha*(3/8 + eS)`.  Term-by-term cancellation is *not* available: the
  identification is pair-with-triple at a common exponent, not pair-with-single.

`hPstar` itself stays correct as an interface (it is a hypothesis and it is verbatim the shifted
part of `Ksum_positivity_three`'s fourteen terms); only its provider needs the rewrite above.

## The bridge statement: design pinned (read before re-review)

The corrected, `P*`-structured interface, with the accounting that must be pinned *before*
the statement goes to review (a wrong coefficient here ships a false lemma past review):

* weights (from `Ksum_positivity_three`): singles `1` each (3 terms), pairs `1/2` each
  (6 terms), signed triples `1/4` each (4 terms), the `s = 1` principal `1`;
* the pole term `P3R (alpha/a)` enters *once*, from the `s = 1` principal functional; the
  four triples are principal but they do **not** add a second `P3R (alpha/a)`: their
  functionals sit at the shifted points `sigma + i*tau` and pair with the *shifted*
  extractions (the pair functionals, which under `chi_1*chi_2*chi_3 = 1` are the
  `chi_l`-functionals at those same shifted points) into
  `P*(t) = Re{P3(alpha/(a+it)) - P3(alpha/(a+lam_1+it)) - P3(alpha/(a+lam_2+it)) - P3(alpha/(a+lam_3+it))}`,
  which is `<= 0` by `Work.ZeroFreeTables.P10.P3star_nonpos` (proved).  So the shifted
  terms contribute **only their eps-terms**, weighted `1/2` (pairs) and `1/4` (triples);
* hence the total error coefficient is `3 * (phi/2) [singles] + 6 * (1/2) * (phi/2) [pairs]
  + 0 [triples, principal]`, and with the real-character value `phi = 1/4` this is
  `3/8 + 3/8 = 3/4` -- the paper's `(a+lam_1)(3/4 + eps)`.  Without the collapse
  (`chi_1*chi_2*chi_3 != 1`) the triples are not principal and the count becomes `7/8`,
  which no longer feeds `p1014_of_extractions`;
* the extraction errors: each of the three single bounds carries `8*(a+lam_1)/(delta*L)`,
  so `24*(a+lam_1)/(delta*L)` must be charged in the eps-budget (cf. the colleague's
  `errBound` in `ScratchHBMine/asmtry.lean`);
* `lam`-hypotheses are part of the interface: `0 <= lam_1`, `lam_1 <= lam_2`,
  `lam_1 <= lam_3` (the free-real-parameter form is false, cf. `Engine.lean`);
* the delegated statement should carry free per-term eps's plus one weighted-sum
  hypothesis, with the *total* coefficient `3/4` in the conclusion -- the per-term eps's
  absorb the `8*alpha/(delta*L)` and the shifted errors.

## STATUS (current) — the statement is case 3, and the inputs now exist

The `Prop` `Engine.HBLemma10_3_engine` now carries the case-3 hypotheses
(`chi_1^2 = chi_2^2 = chi_3^2 = 1`, `chi_1 * chi_2 * chi_3 = 1`, `rho_1.im = 0`),
following the audit recorded in `Engine.lean`: HB derives (10.14) with the `P_3` budget
only in that case; the remaining configurations are the separate `Prop`
`Engine.HB10_3_Fcases`, which is served by the `F`-method (numerical core proved here
as `tf72f_laplace_counterexample_bounds`).

With the statement restricted to case 3, **all analytic inputs exist in the
workspace** and the proof is an assembly:

* the pointwise expansion (10.1)-(10.3): `three_char_combination`/`three_char_nonneg`
  here, and `Ksum_positivity_three` (proved, `Submission.Work.ZeroFreeTables`), which
  gives the same identity at the level of the von Mangoldt sums;
* the per-character point bound (HB §8, the derivative form of Lemma 5.2):
  `Work.ZeroFreeTables.P9.prim.masterP3_assembly.masterP3` (proved), which states
  `SigmaP3L N L chi s a lam_1 <= -P3NearSumL N L chi s a lam_1 delta + (a+lam_1)*(c+e)`
  for primitive non-principal `chi` with `s.re = 1 + a/L`, `|s.im| <= 4`, under
  `LogDerivHyp chi delta L c`; the imprimitive reduction is
  `P9.SigmaP3L_changeLevel_diff` with `P9.weak`;
* which near summands may be kept/dropped: `P9.nearP3sum_ge_kept` (the wanted zero is
  kept) and `P9.NearP3summandNonnegWindow` (all other summands in the window are
  non-negative, so they may be dropped -- this is where `IsMin1WideAt 10` is used);
* the principal/pole term for the point `s = 1` (the `+P_3(alpha/a)` of (10.14)):
  `P9.zetaEngine_principal`;
* the residual step `P*(t) <= 0` under the side condition
  `a^{-3} <= (a+lam_1)^{-3} + (a+lam_2)^{-3} + (a+lam_3)^{-3}` (HB's "the analysis
  leading to Lemma 8.3"): delegated as `ZeroFreeTables/P10/P3star_nonpos`;
* the last step `(a+lam_1)(3/4+eps)` budget `=> 0 <= p1014 delta eps`: proved here as
  `p1014_of_extractions` (it consumes `P_3(1) + P_3(X_2) + P_3(X_3) <= P_3(alpha/a)
  + (6/7)*((3+delta)*C)` with `X_j >= (3+delta)/4` and `C <= 3/4`), together with
  `P3R_mono_103`;
* the certificate (`Lemma10_3Cert[Zero]`) enters only through
  `p1014_neg_of_le_cert`/`p1014_neg_of_nonpos`, i.e. through the contradiction that
  closes the setting.

The collapse of case 3 is what makes the budget `3/4` and not `7/8` or worse: with
`chi_1*chi_2*chi_3 = 1` and all `chi_j` real, `chi_j * chi_k = chi_l` and the four
signed triple characters are principal, so of the eight coefficients only the three
singles (1 each) and the six pairs (1/2 each) carry a `phi/2` error, i.e.
`3*(1/2)*phi + 6*(1/2)*phi/2 * ... = 3 phi = 3/4` at `phi = 1/4` (the real-character
value `1/8` of `lemma3_1_free_gen_real`).

Remaining work: the case-3 bridge, whose conclusion is fixed by the interface of
`p1014_of_extractions`: produce
`P3R 1 + P3R (alpha/(a+lam_2)) + P3R (alpha/(a+lam_3)) <= P3R (alpha/a) + (6/7)*((3+delta)*C)`
with `C <= 3/4` (`alpha = a + lam_1`, `a = 18/7 = 3*(6/7)`, `delta = lam_1/(6/7)`), for
`q >= q_0` depending on `eps`.  The pieces, all proved:

* at `s_j = sigma + i*gamma_j` (`sigma = 1 + a/L`), for the three (primitive reductions
  of the) characters: `P9.prim.masterP3_assembly.masterP3` bounds `SigmaP3L` by
  `-P3NearSumL + (a+lam_1)*(c+e)`; `P9.nearP3sum_ge_kept` converts the *kept* zero
  `rho_j` into `P3R (alpha/(a+lam_j))` up to `8*(a+lam_1)/(delta*L)`, and
  `P9.NearP3summandNonnegWindow` lets the remaining summands be dropped
  (this is where `IsMin1WideAt 10` enters, through `hmin`);
* the pair characters collapse onto the singles (`char_prod_pair_eq_third`) and the
  four signed triple characters are principal (`char_signed_triples_eq_one`), so the
  combination is the sum of the three single terms plus six pair terms, and the
  principal functionals are bounded by the pole term
  `Re P3(alpha/(a + i*tau*L)) <= P3R (alpha/a)` (`P3_shifted_le`);
* the principal functional at `s = 1` itself is bounded by
  `P9.zetaEngine_principal_proof` (proved), whose pole term is exactly
  `Re P3(alpha/((s-1)*L))`;
* the two-sided bookkeeping is `Ksum_positivity_three` (proved);
* the residual `P*(t) <= 0` under `a^{-3} <= sum (a+lam_j)^{-3}` is
  `Work.ZeroFreeTables.P10.P3star_nonpos` (proved, delegated and banked here); it
  derives its rescaling from `P3Pos` -- `Rep9.P3_div_le` is *not* needed for it, nor
  for `P3_shifted_le`.

(The count `C <= 3/4`: singles contribute `3 * (1/2) * phi`, pairs `6 * (1/2) * phi/2`,
triples nothing; with the real-character value `phi = 1/4` of `lemma3_1_free_gen_real`
this is `3/4`.)

## What the target is

With `δ = λ₁/(6/7)` the setting gives `0 ≤ λ₁ ≤ λ₂ ≤ λ₃ ≤ 6/7` (`λ₁ ≤ λ₃` is
`IsMin1WideAt 10` applied to the zero `(χ₃,ρ₃)`), so `δ ∈ [0,1]`; and the proved
certificate says `p1014 δ ε < 0` for `δ ∈ [0,1]`, `ε ≤ 1/1000` (indeed for `ε ≤ 0`).
So the engine at `ε = 1/1000` is *equivalent* to: for large `q`, the setting is
unsatisfiable, i.e. at most two conjugate pairs of characters mod `q` carry a zero
with `λ ≤ 6/7`: HB Lemma 10.3 in sharp form (strictly stronger than the `ε`-form of
the paper and than the workspace input `HBProps.HB10_3_conclusion`).

## Route (HB §10)

* **case 3** (`χ₁χ₂χ₃ = χ₀`, `χ_j` real, `ρ₁` real): the `P₃` method.  The pointwise
  `∏_{j=1}^3 (1 + Re z_j) ≥ 0` (`z_j = χ_j(n)n^{-iγ_j}`) expands
  (`three_char_combination`) into the `K`-combination (10.2)–(10.3); the `P₃`
  analogue of Lemma 5.2 bounds each functional by `−`(near-zero extraction) `+`
  `(a+λ₁)(φ(χ)/2+ε)`; all products collapse (`χ_jχ_k = χ_l`, triples principal), so
  the error coefficient is `3·φ/2 + 3·φ/2 = 3/4` (`φ = 1/4`) — exactly the (10.14)
  budget — and `p1014_of_extractions` converts the extraction bound into
  `0 ≤ p1014 δ ε`.
* **case 1** (the four signed triple characters non-principal): the `F`-method with
  `testFn7_2 (6/7)`, whose Laplace transform is known exactly at the required points
  (see below).  The proved `lemma5_2_of_logDeriv_bound` (error `f 0 (1/6+ε) log q`
  per unit coefficient for a non-principal character) and `lemma5_3` (no `1/6` term
  for the principal character) give the total error `f 0 (7/6 + 8ε) L` for the
  three-character combination: **the `7/6` of HB (10.6) comes out exactly**, uniformly
  in all characters.  Lemma 7.5's identity `λ⁻¹ f 0 = 3F(0) − F(−λ) = 16/15` at
  `λ = 6/7` then turns (10.6) into (10.7)
  `F(−6/7) − F(−λ₁) ≤ 2(F 0 − F(6/7−λ₁)) + O(ε)`, which is false with margin
  `≥ 0.0108` for every `λ₁ ∈ [0, 0.792]`; and the two derivative bounds
  `∫ t f = 16/(35λ)` and `∫ e^{λ t} t f ≥ e^{4/3}·16/(15λ)` plus
  `log(7/6) ≥ 11/72` give `(10.7) ⇒ λ₁ ≤ 0.792`.  Contradiction.
* **case 2** (`χ₁χ₂χ₃ = χ₀` with some `χ_j` complex): here exactly one of the four signed
  triples is principal, and its extra `(1/4)F(−λ₁)` term breaks the margin of the
  case-1 argument — this is the case the paper handles by Lemma 10.2 (the
  `(10.8)`–`(10.12)` computation).  It is the remaining gap.

### Numerical content of the `F`-method (proved, delegated)

`tf72f_laplace_counterexample_bounds` (in this workspace):

* `∫_0^{7/3} e^{(792/1000)t} f(t) dt ≤ 761/500`, i.e. `F(−0.792) ≤ 1.522`, and
* `∫_0^{7/3} e^{−(57/875)t} f(t) dt ≥ 1709/2000`, i.e. `F(57/875) ≥ 0.8545`,

for `f = tf72f (6/7)`.  With `F 0 = 8/9` and `F (−6/7) = 8/5` these give
`F(−6/7) − F(−λ₁) ≥ 0.0783` and `2(F 0 − F(6/7−λ₁)) ≤ 0.0765` for `λ₁ ≤ 0.792`
(margin `≥ 0.0108` at `λ₁ = 0.792`, decreasing in `λ₁`, so `λ₁ = 0.792` is the worst point),
against which the `ε`-correction `8ε f 0 = 7.31ε` is harmless for `ε ≤ 1/2000`.

Below: the certificate in the form the contradiction uses, elementary consequences of
the setting, the three-character combination identity of (10.1)–(10.3), the final
algebra step, and the `F`-method's numerical core.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg
import Submission.Work.ZeroFreeTables.EngineRoadmap
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P3.WLBase
import Submission.Work.ZeroFreeTables.P3.CompletedDerivPF
import Submission.Work.ZeroFreeTables.P3.SideConditions
import Submission.Work.ZeroFreeTables.P3.P3Bounds
import Submission.Work.ZeroFreeTables.P3.CaseC_D
import Submission.Work.ZeroFreeTables.P3.Imports
import Submission.Work.ZeroFreeTables.P3Pos
import Submission.Work.ZeroFreeTables.TrigPolyPos
import Submission.Work.ZeroFreeTables.ksum_trigPoly_nonneg
import Submission.Work.ZeroFreeTables.Lemma10_3Cert
import Submission.Work.ZeroFreeTables.HB4_1
import Submission.Work.ZeroFreeTables.P10.P3star_nonpos
import Submission.Work.ZeroFreeTables.P10.shifted_extract_of_point_bound
import Submission.Work.ZeroFreeTables.P9.nearP3sum_ge_kept
import Submission.Work.ZeroFreeTables.P9.P3NearSumL_eq_nearP3sum
import Submission.Work.ZeroFreeTables.P9.prim.masterP3_assembly
import Submission.Work.ZeroFreeTables.P9.NearP3summandNonnegWindow
import Submission.Work.ZeroFreeTables.Ksum_positivity_three
import Submission.Work.ZeroFreeTables.tf72f_laplace_counterexample_bounds
import Submission.Work.ZeroFreeTables.XY.ImprimitiveSigmaReduce
import Submission.Work.ZeroFreeTables.XY.Lam1Lower
import Submission.Work.ZeroFreeTables.HB95h2.logDerivEighth
import Submission.Work.P10.PrincipalSigmaBound_18_7
import Submission.Work.P10.Pstar_collapse
import Submission.Work.ZeroFreeTables.P10.Defs14
import Submission.Work.ZeroFreeTables.P10.summable_hbTermG
import Submission.Work.ZeroFreeTables.HB103.Comb14Positivity

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

open Work.LinnikContract

/-! ## 1. The certificate in the form the contradiction uses -/

/-- `p1014` is monotone in `ε` (for `δ ≥ -3`, so that `3 + δ ≥ 0`). -/
theorem p1014_mono_eps {δ : ℝ} (hδ : -3 ≤ δ) {ε ε' : ℝ} (hε : ε ≤ ε') :
    p1014 δ ε ≤ p1014 δ ε' := by
  have h3 : (0:ℝ) ≤ 3 + δ := by linarith only [hδ]
  unfold p1014
  linarith only [mul_le_mul_of_nonneg_left hε h3, hε, h3]

/-- **The certificate, monotone form**: `p1014 δ ε < 0` for `δ ∈ [0,1]` and `ε ≤ 1/1000`. -/
theorem p1014_neg_of_le_cert {δ ε : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : ε ≤ 1/1000) :
    p1014 δ ε < 0 :=
  lt_of_le_of_lt (p1014_mono_eps (by linarith only [hδ0]) hε) (Lemma10_3Cert δ hδ0 hδ1)

/-- The same at `ε = 0` (from `Lemma10_3CertZero`). -/
theorem p1014_neg_of_nonpos {δ ε : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hε : ε ≤ 0) :
    p1014 δ ε < 0 :=
  lt_of_le_of_lt (p1014_mono_eps (by linarith only [hδ0]) hε) (Lemma10_3CertZero δ hδ0 hδ1)

/-! ## 2. Elementary consequences of the setting -/

/-- In the setting, `λ₁ ≤ λ₃`: the wide minimality `IsMin1WideAt 10 χ₁ ρ₁` applies to
the zero `(χ₃,ρ₃)` (`|Im ρ₃| ≤ 1 ≤ 10`). -/
theorem lamOf_ρ₁_le_ρ₃ {q : ℕ} [NeZero q] {χ₁ χ₃ : DirichletCharacter ℂ q} {ρ₁ ρ₃ : ℂ}
    (hm : IsMin1WideAt 10 χ₁ ρ₁) (h3 : IsZ χ₃ ρ₃) : lamOf q ρ₁ ≤ lamOf q ρ₃ :=
  hm.2 χ₃ ρ₃ h3.1 h3.2.1 (le_trans h3.2.2 (by norm_num))

/-- `λ` is non-negative for a zero with `Re ρ ≤ 1`; this puts `δ = λ₁/(6/7)` in `[0,1]`. -/
theorem lamOf_nonneg_of_re_le_one {q : ℕ} {ρ : ℂ} (hre : ρ.re ≤ 1) :
    0 ≤ lamOf q ρ := by
  unfold lamOf
  have : (0:ℝ) ≤ 1 - ρ.re := by linarith only [hre]
  exact mul_nonneg this (Real.log_natCast_nonneg q)

/-! ## 3. HB (10.1)–(10.3): the three-character combination

For `z_j = χ_j(n) n^{-iγ_j}` (so `‖z_j‖ ≤ 1`), the pointwise `∏_{j=1}^3 (1 + Re z_j) ≥ 0`
of (10.1) expands, with `Re z = (z + z̄)/2`, into the `K`-combination (10.2)–(10.3). -/

/-- **HB (10.1) expanded** (algebraic identity in `z₁ z₂ z₃ ∈ ℂ`). -/
theorem three_char_combination (z₁ z₂ z₃ : ℂ) :
    (1 + z₁.re) * (1 + z₂.re) * (1 + z₃.re)
      = 1 + (z₁.re + z₂.re + z₃.re)
        + (1/2) * ((z₁ * z₂).re + (z₁ * (starRingEnd ℂ) z₂).re + (z₁ * z₃).re
            + (z₁ * (starRingEnd ℂ) z₃).re + (z₂ * z₃).re + (z₂ * (starRingEnd ℂ) z₃).re)
        + (1/4) * ((z₁ * z₂ * z₃).re + (z₁ * z₂ * (starRingEnd ℂ) z₃).re
            + (z₁ * (starRingEnd ℂ) z₂ * z₃).re + ((starRingEnd ℂ) z₁ * z₂ * z₃).re) := by
  simp only [Complex.mul_re, Complex.mul_im]
  simp
  ring

/-- **HB (10.1)**: the combination is non-negative whenever `‖z_j‖ ≤ 1`. -/
theorem three_char_nonneg (z₁ z₂ z₃ : ℂ) (h₁ : ‖z₁‖ ≤ 1) (h₂ : ‖z₂‖ ≤ 1) (h₃ : ‖z₃‖ ≤ 1) :
    0 ≤ (1 + z₁.re) * (1 + z₂.re) * (1 + z₃.re) := by
  have e₁ : 0 ≤ 1 + z₁.re := by
    have h := Complex.abs_re_le_norm z₁
    rw [abs_le] at h
    linarith only [h.1, h₁, h]
  have e₂ : 0 ≤ 1 + z₂.re := by
    have h := Complex.abs_re_le_norm z₂
    rw [abs_le] at h
    linarith only [h.1, h₂, h]
  have e₃ : 0 ≤ 1 + z₃.re := by
    have h := Complex.abs_re_le_norm z₃
    rw [abs_le] at h
    linarith only [h.1, h₃, h]
  exact mul_nonneg (mul_nonneg e₁ e₂) e₃

/-! ## 4. The case-3 collapse (character algebra)

With `chi_j^2 = 1` and `chi_1 * chi_2 * chi_3 = 1` the product of two of the
characters is the third one; consequently the four signed triple products are all
principal.  This is the collapse that reduces the `K`-combination (10.2)-(10.3) to
(10.13) in case 3. -/

lemma char_prod_pair_eq_third {q : ℕ} [NeZero q] {χ₁ χ₂ χ₃ : DirichletCharacter ℂ q}
    (h2 : χ₂ ^ 2 = 1) (h3 : χ₃ ^ 2 = 1) (h : χ₁ * χ₂ * χ₃ = 1) : χ₁ * χ₂ = χ₃ := by
  have key : χ₁ * χ₂ * (χ₃ * χ₃) = χ₃ := by
    rw [← mul_assoc, h, one_mul]
  rwa [← sq, h3, mul_one] at key

/-- In case 3 each `chi_j` is its own inverse. -/
lemma inv_eq_self_of_sq_eq_one {q : ℕ} [NeZero q] {χ₁ : DirichletCharacter ℂ q}
    (h : χ₁ ^ 2 = 1) : χ₁⁻¹ = χ₁ := by
  have h' : χ₁ * χ₁ = 1 := by rwa [sq] at h
  exact inv_eq_of_mul_eq_one_right h'

lemma char_signed_triples_eq_one {q : ℕ} [NeZero q] {χ₁ χ₂ χ₃ : DirichletCharacter ℂ q}
    (h1 : χ₁ ^ 2 = 1) (h2 : χ₂ ^ 2 = 1) (h3 : χ₃ ^ 2 = 1) (h : χ₁ * χ₂ * χ₃ = 1) :
    (χ₁ * χ₂ * χ₃⁻¹ = 1) ∧ (χ₁ * χ₂⁻¹ * χ₃ = 1) ∧ (χ₁⁻¹ * χ₂ * χ₃ = 1) := by
  have i1 := inv_eq_self_of_sq_eq_one h1
  have i2 := inv_eq_self_of_sq_eq_one h2
  have i3 := inv_eq_self_of_sq_eq_one h3
  exact ⟨by rw [i3, h], by rw [i2, h], by rw [i1, h]⟩

-- The four signed triple products of case 3 are principal: the first by
-- hypothesis, the other three by `inv_eq_self_of_sq_eq_one`.  Together with
-- `char_prod_pair_eq_third` this is the collapse that removes the four triple
-- terms from the `phi`-bookkeeping of (10.2)-(10.3), leaving the three singles
-- and six pairs, i.e. the budget `3 * (1/2) * (1/4) + 6 * (1/2) * (1/8) = 3/4`.


/-! ## 5. The pole term at the test point

`zetaEngine_principal_proof` bounds the principal-character functional by
`Re P3(alpha/((s-1)*L))`; at `s = 1 + a/L` (`a = 18/7`, `alpha = a + lam_1`) this is
exactly `P3R (alpha/a)`, the head of (10.14). -/

/-- `P3` at a real argument is `P3R`. -/
theorem P3R_eq_re_P3 (x : ℝ) : (P3 (x : ℂ)).re = P3R x := by
  have h : P3 (x : ℂ) = ((P3R x : ℝ) : ℂ) := by
    simp only [P3, P3R]
    push_cast
    ring
  rw [h, Complex.ofReal_re]

/-- **The pole term at `s = 1 + a/L` is `P3R (alpha/a)`.**  (The argument is
`alpha/(((1 + a/L) - 1) * L) = alpha/a`.) -/
theorem P3_pole_eq {α a L : ℝ} (ha : a ≠ 0) (hL : L ≠ 0) :
    (P3 (α / (((((1 + a / L : ℝ)) : ℂ) - 1) * (L : ℂ)))).re = P3R (α / a) := by
  have h1 : ((((1 + a / L : ℝ)) : ℂ) - 1) = ((a / L : ℝ) : ℂ) := by
    push_cast
    ring
  have h2 : (((a / L : ℝ)) : ℂ) * (L : ℂ) = (a : ℂ) := by
    rw [← Complex.ofReal_mul, div_mul_cancel₀ a hL]
  have harg : (α / (((((1 + a / L : ℝ)) : ℂ) - 1) * (L : ℂ))) = (((α / a : ℝ)) : ℂ) := by
    rw [h1, h2]
    rw [← Complex.ofReal_div]
  rw [harg, P3R_eq_re_P3]

/-! ## 6. The kept-zero term is the head of (10.14)

The bridge's opening move: at the zero's *own* point the zero term of the near sum is
exactly `P3R (alpha/(a+lam))` --- the `X_j` that `p1014_of_extractions` consumes.
The local copies of the test point and of the argument computation are named with a
`P10` prefix so that they cannot clash with the same-named items of
`HBLemma9_1_proof` in a consolidated build. -/

/-- The test point `sigma + i*t`, `sigma = 1 + a/L`. -/
def P10sPt (a L t : ℝ) : ℂ := ((1 + a / L : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I

/-- `(sigma + i*t - rho)*L` for a zero `rho = (1 - lam/L) + i*gamma`. -/
theorem P10sPt_sub_mul_eq {a L lam γ t : ℝ} (hL : L ≠ 0) {ρ : ℂ}
    (hre : ρ.re = 1 - lam / L) (him : ρ.im = γ) :
    (P10sPt a L t - ρ) * (L : ℂ)
      = ((a + lam : ℝ) : ℂ) + (((t - γ) * L : ℝ) : ℂ) * Complex.I := by
  have h1 : (P10sPt a L t).re = 1 + a / L := by simp [P10sPt]
  have h2 : (P10sPt a L t).im = t := by simp [P10sPt]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero, zero_add, sub_zero, h1, h2, hre, him] <;>
    field_simp <;> ring

/-- **The kept-zero term is `P3R (alpha/(a+lam))`.** -/
theorem P10_zero_term_eq {α a lam L : ℝ} (hL : L ≠ 0) (hsum : a + lam ≠ 0) {ρ : ℂ}
    (hre : ρ.re = 1 - lam / L) :
    (P3 (α / ((P10sPt a L ρ.im - ρ) * (L : ℂ)))).re
      = P3R (α / (a + lam)) := by
  rw [P10sPt_sub_mul_eq hL hre rfl, show (ρ.im - ρ.im) * L = 0 by ring]
  rw [Complex.ofReal_zero, zero_mul, add_zero]
  rw [← Complex.ofReal_div]
  exact P3R_eq_re_P3 _

/-! ## 7. The kept zero is bounded by the near sum

The second half of the kept/dropped bookkeeping: the near sum — whose *other* summands
are non-negative (`P9.NearP3summandNonnegWindow`, via the window hypothesis
`lam_1 <= (1 - u.re)*L` coming from `IsMin1WideAt 10`) — dominates the kept term.  This
is `P9.nearP3sum_ge_kept` at the singleton `T = {rho}`, with the kept term identified by
`P10_zero_term_eq`.  `P9.P3NearSumL_eq_nearP3sum` shows `nearP3sum` *is* `P3NearSumL`
for primitive `chi`, so this composes with the `masterP3` bound. -/

/-- **The kept zero is at most the near sum plus `8*(a+lam_1)/(delta*L)`.** -/
theorem kept_le_near_sum {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    {L a lam1 lam δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hlam1 : 0 ≤ lam1)
    (hlam : 0 ≤ lam) (hδ : 0 < δ) (hδ1 : δ < 1) (haδ : 2 * a ≤ δ * L)
    {ρ : ℂ} (hzero : Work.LinnikContract.zeroMult chi ρ ≠ 0)
    (him : |ρ.im| ≤ 3) (hre : ρ.re = 1 - lam / L)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult chi u ≠ 0 → |u.im| ≤ 10 →
      lam1 ≤ (1 - u.re) * L) :
    P3R ((a + lam1) / (a + lam))
      ≤ Work.ZeroFreeTables.P9.nearP3sum N L chi (P10sPt a L ρ.im) a lam1 δ
        + 8 * (a + lam1) / (δ * L) := by
  have hsum : a + lam ≠ 0 := by positivity
  have hsre : (P10sPt a L ρ.im).re = 1 + a / L := by simp [P10sPt]
  have hsim : |(P10sPt a L ρ.im).im| ≤ 3 := by simpa [P10sPt] using him
  have h10 : |ρ.im| ≤ 10 := by linarith only [abs_nonneg ρ.im, him, hδ, hδ1]
  have h := Work.ZeroFreeTables.P9.nearP3sum_ge_kept chi hchi hL ha hlam1 hδ hδ1 haδ
    hsre hsim hmin ({ ρ } : Finset ℂ)
    (by intro u hu
        rw [Finset.mem_singleton] at hu
        subst hu
        exact hzero)
    (by intro u hu
        rw [Finset.mem_singleton] at hu
        subst hu
        exact h10)
  rw [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul] at h
  have hval : (P3 (((a : ℂ) + (lam1 : ℂ)) / ((P10sPt a L ρ.im - ρ) * (L : ℂ)))).re
      = P3R ((a + lam1) / (a + lam)) := by
    rw [show ((a : ℂ) + (lam1 : ℂ)) = ((a + lam1 : ℝ) : ℂ) by push_cast; ring]
    exact P10_zero_term_eq (α := a + lam1) (a := a) (lam := lam) (L := L) (ne_of_gt hL) hsum hre
  rw [hval] at h
  exact h

/-- **The near sum dominates the kept term up to the budget.**  (The sign convention
the combination consumes: `masterP3` gives `SigmaP3L <= -nearP3sum + error`, so one needs
`P3R (alpha/(a+lam)) - 8*(a+lam_1)/(delta*L) <= nearP3sum`.) -/
theorem near_sum_ge_kept {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    {L a lam1 lam δ : ℝ} (hL : 0 < L) (ha : 0 < a) (hlam1 : 0 ≤ lam1)
    (hlam : 0 ≤ lam) (hδ : 0 < δ) (hδ1 : δ < 1) (haδ : 2 * a ≤ δ * L)
    {ρ : ℂ} (hzero : Work.LinnikContract.zeroMult chi ρ ≠ 0)
    (him : |ρ.im| ≤ 3) (hre : ρ.re = 1 - lam / L)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult chi u ≠ 0 → |u.im| ≤ 10 →
      lam1 ≤ (1 - u.re) * L) :
    P3R ((a + lam1) / (a + lam)) - 8 * (a + lam1) / (δ * L)
      ≤ Work.ZeroFreeTables.P9.nearP3sum N L chi (P10sPt a L ρ.im) a lam1 δ := by
  linarith [kept_le_near_sum chi hchi hL ha hlam1 hlam hδ hδ1 haδ hzero him hre hmin]

/-! ## 8. Monotonicity of `P₃ℝ` -/

/-- `P₃` is monotone on `[0,∞)` (`P₃(X) = X + X² + (2/3)X³`). -/
theorem P3R_mono_103 {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : P3R x ≤ P3R y := by
  have h0 : 0 ≤ y - x := by linarith only [hxy]
  have hkey : P3R y - P3R x = (y - x) * (1 + (x + y) + (2/3) * (x^2 + x*y + y^2)) := by
    unfold P3R; ring
  have hfac : 0 ≤ 1 + (x + y) + (2/3) * (x^2 + x*y + y^2) := by
    linarith only [sq_nonneg (x + y), sq_nonneg x, sq_nonneg y, hx, hxy]
  nlinarith only [hkey, h0, hfac, hxy]

-- The principal-character terms sit at the *shifted* points `sigma + i*tau` (the four
-- triple characters of case 3 are principal); their domination by the unshifted
-- `P3R (alpha/a)` is `P3_shifted_le` above, proved from the sharp identity
-- `Work.ZeroFreeTables.P3_re_eq` of `P3Pos`.  The rescaling comparison `Rep9.P3_div_le`
-- is the same engine that drives the residual step `P3star_nonpos`.

/-! ## 9. The pole term at a shifted point

In case 3 the four triple characters are principal, so their functionals sit at the
shifted points `sigma + i*tau` and their bound is the pole term
`Re P3(alpha/(a + i*tau*L))`.  For the (10.14) budget each such term must be
dominated by the unshifted `P3R (alpha/a)`: this is `P3_shifted_le`. -/

/-- **The pole term at a shifted point is dominated by the unshifted one.**

With `w = alpha/(a + i t)` (`a, alpha > 0`) one has `Re w <= alpha/a`, `0 <= Re w`
and `(Re w)^2 <= normSq w`, so the sharp identity
`Re P3(w) = (8/3)(Re w)^3 + (1 + 2 Re w)(Re w - normSq w)` of `P3Pos` gives
`Re P3(w) <= P3R(Re w) <= P3R(alpha/a)`. -/
theorem P3_shifted_le {α a t : ℝ} (ha : 0 < a) (hα : 0 < α) :
    (P3 (α / ((a : ℂ) + (t : ℂ) * Complex.I))).re ≤ P3R (α / a) := by
  set w : ℂ := α / ((a : ℂ) + (t : ℂ) * Complex.I) with hw
  have hden : (0 : ℝ) < a ^ 2 + t ^ 2 := by positivity
  have hre : w.re = α * a / (a ^ 2 + t ^ 2) := by
    rw [hw, Complex.div_re]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
    ring
  have hns : Complex.normSq w = α ^ 2 / (a ^ 2 + t ^ 2) := by
    have him : w.im = -(α * t) / (a ^ 2 + t ^ 2) := by
      rw [hw, Complex.div_im]
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.normSq_apply]
      ring
    rw [Complex.normSq_apply, hre, him]
    field_simp
  have hu0 : 0 ≤ w.re := by rw [hre]; positivity
  have hle : w.re ≤ α / a := by
    rw [hre, div_le_div_iff₀ hden ha]
    nlinarith only [sq_nonneg t, le_of_lt ha, le_of_lt hα, hα]
  have hsquare : w.re ^ 2 ≤ Complex.normSq w := by
    rw [Complex.normSq_apply]
    linarith only [sq_nonneg w.im]
  have h1 : 0 ≤ 1 + 2 * w.re := by linarith only [hu0]
  have hper : P3R w.re = (8 / 3) * w.re ^ 3 + (1 + 2 * w.re) * (w.re - w.re ^ 2) := by
    unfold P3R
    ring
  have hmain : (P3 w).re ≤ P3R w.re := by
    rw [P3_re_eq, hper]
    have hkey : w.re - Complex.normSq w ≤ w.re - w.re ^ 2 := by linarith only [hsquare]
    linarith only [mul_le_mul_of_nonneg_left hkey h1, hkey, h1]
  exact le_trans hmain (P3R_mono_103 hu0 hle)

/-! ## 10. The pole term at a shifted point, in `zetaEngine_principal_proof`'s form

`zetaEngine_principal_proof` bounds the principal functional by `Re P3(alpha/((s-1)*L))`.
At a shifted point `s = sigma + i*tau` that argument is `((sigma + i*tau) - 1)*L`; it
must be identified with `a + i*(tau*L)`, the form `P3_shifted_le` consumes, before the
shifted principal terms can be collapsed into the budget term `P3R (alpha/a)`. -/

/-- **The shifted pole argument is `a + i*(tau*L)`.** -/
theorem P3_pole_shift_eq {α a L τ : ℝ} (hL : L ≠ 0) :
    (P3 (α / ((((1 + a / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I - 1) * (L : ℂ)))).re
      = (P3 (α / ((a : ℂ) + (((τ * L : ℝ)) : ℂ) * Complex.I))).re := by
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have h1 : (((1 + a / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I - 1)
      = (((a / L : ℝ)) : ℂ) + (τ : ℂ) * Complex.I := by
    push_cast
    ring
  have h2 : (((((a / L : ℝ)) : ℂ) + (τ : ℂ) * Complex.I) * (L : ℂ))
      = (a : ℂ) + (((τ * L : ℝ)) : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [h1, h2]

/-- **The shifted pole term is at most `P3R (alpha/a)`** (for `a, alpha > 0`). -/
theorem P3_pole_shift_le {α a L τ : ℝ} (hL : L ≠ 0) (ha : 0 < a) (hα : 0 < α) :
    (P3 (α / ((((1 + a / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I - 1) * (L : ℂ)))).re
      ≤ P3R (α / a) := by
  rw [P3_pole_shift_eq hL]
  exact P3_shifted_le ha hα

/-! ## 11. The single-character extraction bound

The usable form of the point bound for one character: given `masterP3`'s conclusion at
the zero's own point (`SigmaP3L <= -P3NearSumL + (a+lam_1)(c+e)` -- the caller supplies
the threshold `L₀`), the kept-zero bookkeeping (`near_sum_ge_kept`, transported across
the free equality `P3NearSumL = nearP3sum`, which holds for primitive `chi` and
`0 < delta <= 1`) turns the near sum into the extracted term.  This is the shape the
weighted combination consumes for each of the three characters. -/

/-- **The single-character extraction bound.** -/
theorem extract_of_point_bound {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    (hprim : chi.IsPrimitive) {a δ c e lam1 lam L : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hL : 0 < L) (ha : 0 < a) (hlam1 : 0 ≤ lam1) (hlam : 0 ≤ lam) (haδ : 2 * a ≤ δ * L)
    {ρ : ℂ} (hzero : Work.LinnikContract.zeroMult chi ρ ≠ 0)
    (him : |ρ.im| ≤ 3) (hre : ρ.re = 1 - lam / L)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult chi u ≠ 0 → |u.im| ≤ 10 →
      lam1 ≤ (1 - u.re) * L)
    (hm : Work.ZeroFreeTables.SigmaP3L N L chi (P10sPt a L ρ.im) a lam1
      ≤ -Work.ZeroFreeTables.P3NearSumL N L chi (P10sPt a L ρ.im) a lam1 δ
        + (a + lam1) * (c + e)) :
    Work.ZeroFreeTables.SigmaP3L N L chi (P10sPt a L ρ.im) a lam1
      ≤ -P3R ((a + lam1) / (a + lam)) + 8 * (a + lam1) / (δ * L)
        + (a + lam1) * (c + e) := by
  rw [Work.ZeroFreeTables.P9.P3NearSumL_eq_nearP3sum chi hchi hprim hδ (le_of_lt hδ1)
      a lam1 L] at hm
  have hkept := near_sum_ge_kept chi hchi hL ha hlam1 hlam hδ hδ1 haδ hzero him hre hmin
  linarith [hm, hkept]

/-! ## 12. The pair-functional bound (the near sum drops)

For a character whose zeros are all *outside* the extraction (the pair characters
`chi_j*chi_k = chi_l`, and the principal case on the far side of the collapse) nothing has
to be kept out of the near sum: every summand is non-negative inside the `delta`-window
(`P9.NearP3summandNonnegWindow`, whose window hypothesis is what `IsMin1WideAt 10`
supplies), so `P3NearSumL >= 0` and `masterP3`'s bound loses its near-sum term. -/

/-- **The pair-functional bound: `SigmaP3L <= (a+lam_1)(c+e)` with the near sum dropped.** -/
theorem pair_point_bound {N : ℕ} [NeZero N] (psi : DirichletCharacter ℂ N) (hpsi : psi ≠ 1)
    (hprim : psi.IsPrimitive) {a δ c e lam1 L : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hL : 0 < L) (ha : 0 < a) (hlam1 : 0 ≤ lam1) {s : ℂ} (hsre : s.re = 1 + a / L)
    (hwin : ∀ u : ℂ, Work.LinnikContract.zeroMult psi u ≠ 0 →
      ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → lam1 ≤ (1 - u.re) * L)
    (hm : Work.ZeroFreeTables.SigmaP3L N L psi s a lam1
      ≤ -Work.ZeroFreeTables.P3NearSumL N L psi s a lam1 δ + (a + lam1) * (c + e)) :
    Work.ZeroFreeTables.SigmaP3L N L psi s a lam1 ≤ (a + lam1) * (c + e) := by
  have hα : 0 < a + lam1 := by linarith only [ha, hlam1]
  have hnn : 0 ≤ Work.ZeroFreeTables.P3NearSumL N L psi s a lam1 δ := by
    rw [Work.ZeroFreeTables.P9.P3NearSumL_eq_nearP3sum psi hpsi hprim hδ (le_of_lt hδ1) a lam1 L,
      Work.ZeroFreeTables.P9.nearP3sum_eq_tsum]
    exact tsum_nonneg (fun u =>
      Work.ZeroFreeTables.P9.NearP3summandNonnegWindow psi hL hα hsre hwin u)
  linarith [hm, hnn]

/-! ## 13. The arithmetic interface of the weighted combination

Once the weighted sum of the bounds has been assembled (weights `1, 1, 1/2, 1/4` from
`Ksum_positivity_three`, with `P3R (alpha/a)` collecting the pole terms), the remaining
step is pure arithmetic: this is the shape `p1014_of_extractions` consumes. -/

/-- **The weighted sum of the bounds, rearranged into the extraction inequality.** -/
theorem extraction_of_weighted_sum {a lam1 lam2 lam3 ε C : ℝ}
    (ha : 0 < a) (hlam1 : 0 ≤ lam1) (hC : C ≤ 3 / 4 + ε)
    (h : 0 ≤ -P3R ((a + lam1) / (a + lam1)) - P3R ((a + lam1) / (a + lam2))
            - P3R ((a + lam1) / (a + lam3)) + P3R ((a + lam1) / a) + (a + lam1) * C) :
    P3R 1 + P3R ((a + lam1) / (a + lam2)) + P3R ((a + lam1) / (a + lam3))
      ≤ P3R ((a + lam1) / a) + (a + lam1) * (3 / 4 + ε) := by
  have hpos : a + lam1 ≠ 0 := by positivity
  rw [div_self hpos] at h
  have hnn : 0 ≤ a + lam1 := by linarith only [ha, hlam1]
  have hmul : (a + lam1) * C ≤ (a + lam1) * (3 / 4 + ε) :=
    mul_le_mul_of_nonneg_left hC hnn
  linarith only [h, hmul]

/-- **HB (10.14) from the extraction bound of the `P₃` derivation.**

If the near-zero extractions of the `P₃` functionals together with the error budget give
`P₃(1) + P₃(X₂) + P₃(X₃) ≤ P₃(α/a) + (6/7)·((3+δ)·C)`, `a = 18/7`, `α = a + λ₁`, and
`X_j ≥ (3+δ)/4` (true for `X_j = α/(a+λ_j)` when `λ_j ≤ 6/7`), then `0 ≤ p1014 δ ε`
as soon as `(6/7)·C ≤ 9/14`, i.e. `C ≤ 3/4`. -/
theorem p1014_of_extractions {δ ε C X₁ X₂ X₃ : ℝ} (hδ0 : 0 ≤ δ) (hε : 0 ≤ ε)
    (hC : (6/7) * C ≤ 9/14) (hX₁ : X₁ = (3 + δ) / 3)
    (hX₂ : (3 + δ) / 4 ≤ X₂) (hX₃ : (3 + δ) / 4 ≤ X₃)
    (h : P3R 1 + P3R X₂ + P3R X₃ ≤ P3R X₁ + (6/7) * ((3 + δ) * C)) :
    0 ≤ p1014 δ ε := by
  have hY : 0 ≤ (3 + δ) / 4 := by linarith only [hδ0]
  have hm₂ : P3R ((3 + δ) / 4) ≤ P3R X₂ := P3R_mono_103 hY hX₂
  have hm₃ : P3R ((3 + δ) / 4) ≤ P3R X₃ := P3R_mono_103 hY hX₃
  have hpos : (0:ℝ) < 3 + δ := by linarith only [hδ0]
  have hbudget : (6/7) * ((3 + δ) * C) ≤ (3 + δ) * (9/14) := by
    nlinarith only [hC, le_of_lt hpos, hδ0]
  have hmain : P3R 1 + 2 * P3R ((3 + δ) / 4) ≤ P3R ((3 + δ) / 3) + (3 + δ) * (9/14) := by
    rw [hX₁] at h
    linarith only [h, hm₂, hm₃, hbudget]
  have hε' : 0 ≤ (3 + δ) * ε := mul_nonneg (le_of_lt hpos) hε
  unfold p1014
  linarith only [hmain, hε']

/-! ## 15. The target

The remaining inputs are the `P₃` functional bound of §8 (case 3) and the `F`-method
derivation of (10.6)–(10.7) (cases 1, and the paper's Lemma 10.2 for case 2); the exact
state of that assembly is recorded in the roadmap at the head of this file. -/

/-! ## 14b. HB (10.14) from the bridge in the form `case3_weighted_combination` delivers it

`case3_weighted_combination` produces the residual bound with the *error budget* `eps` on the
right (`P3R 1 + P3R X₂ + P3R X₃ ≤ P3R X₁ + (a+λ₁)(3/4 + eps)`), while `p1014` carries the
free `ε` of the engine.  Comparing the two (`a = 18/7`, `λ₁ = (6/7)δ`) leaves exactly
`(3+δ)(ε − (6/7)eps)`, so the engine's `ε` dominates `eps` up to the factor `7/6`. -/
theorem p1014_of_bridge_eps {X₁ X₂ X₃ δ eps ε : ℝ} (hδ0 : 0 ≤ δ) (hX₁ : X₁ = (3 + δ) / 3)
    (hX₂ : (3 + δ) / 4 ≤ X₂) (hX₃ : (3 + δ) / 4 ≤ X₃)
    (hε0 : 0 ≤ ε) (heps : eps ≤ (7/6) * ε)
    (h : P3R 1 + P3R X₂ + P3R X₃
      ≤ P3R X₁ + ((18/7 : ℝ) + (6/7) * δ) * (3/4 + eps)) :
    0 ≤ p1014 δ ε := by
  have hY : 0 ≤ (3 + δ) / 4 := by linarith only [hδ0]
  have hm₂ : P3R ((3 + δ) / 4) ≤ P3R X₂ := P3R_mono_103 hY hX₂
  have hm₃ : P3R ((3 + δ) / 4) ≤ P3R X₃ := P3R_mono_103 hY hX₃
  have h3δ : (0:ℝ) ≤ 3 + δ := by linarith only [hδ0]
  have hrew : ((18/7 : ℝ) + (6/7) * δ) * (3/4 + eps) = (6/7) * ((3 + δ) * (3/4 + eps)) := by ring
  rw [hrew] at h
  have hkey : (3 + δ) * ((6/7) * eps) ≤ (3 + δ) * ε :=
    mul_le_mul_of_nonneg_left (by linarith only [heps]) h3δ
  unfold p1014
  rw [← hX₁]
  linarith only [h, hm₂, hm₃, hkey, h3δ, mul_nonneg h3δ hε0]

/-! ## 14c. The `λ`-facts of the setting (used by the final assembly)

`0 ≤ λ_j` needs the zero-free strip `0 < Re ρ < 1` of the completed L-function
(`isZ_lambda_nonneg`, i.e. `0 < Re ρ < 1`), and `λ₁ ≤ λ_j` is the *wide* minimality
`IsMin1WideAt 10` applied to the zero `ρ_j` (`|ρ_j.im| ≤ 1 ≤ 10`). -/
theorem lamOf_nonneg_of_isZ_103 {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    {ρ : ℂ} (h : IsZ χ ρ) : 0 ≤ lamOf q ρ :=
  Work.LinnikContract.API.isZ_lambda_nonneg hq h

theorem lamOf_le_of_isMin1Wide {q : ℕ} [NeZero q] {χ₁ χ : DirichletCharacter ℂ q}
    {ρ₁ ρ : ℂ} (hm : IsMin1WideAt 10 χ₁ ρ₁) (h : IsZ χ ρ) :
    lamOf q ρ₁ ≤ lamOf q ρ :=
  hm.2 χ ρ h.1 h.2.1 (le_trans h.2.2 (by norm_num))

/-! ## 14d. `P₃` helpers and the thresholded extraction at a fixed level

`P10.SigmaP3L_le_extract_of_character` asks for the HB Lemma 3.1 input *without* a lower
threshold on the scale.  `HB95h2.logDerivEighth` supplies it only above a threshold `L0`,
so the engine uses the variant `SigmaP3L_extract_at` below: the thresholds `Lm` (of
`masterP3`) and `Li` (of `ImprimitiveSigmaReduce`) are exposed, and the HB Lemma 3.1 input
is a hypothesis of the caller at the single scale `log q`. -/

/-- `Re P₃(x) = P₃ℝ(x)` at a real argument, in division form. -/
theorem P3_ofReal_div_eq_P3R (α A : ℝ) :
    (P3 ((α : ℂ) / (A : ℂ))).re = P3R (α / A) := by
  rw [← Complex.ofReal_div]
  exact P3R_eq_re_P3 _

/-- The same with the imaginary part of the denominator vanishing. -/
theorem P3_div_ofReal_eq_P3R {α A t : ℝ} (ht : t = 0) :
    (P3 (α / ((A : ℂ) + (t : ℂ) * Complex.I))).re = P3R (α / A) := by
  rw [ht, Complex.ofReal_zero, zero_mul, add_zero]
  exact P3_ofReal_div_eq_P3R α A

/-- In case 3 (`χ₁² = χ₂² = χ₃² = 1`, `χ₁χ₂χ₃ = 1`) each pair product is the remaining
character. -/
theorem char_pair_prod_eq_third {q : ℕ} [NeZero q] {χ₁ χ₂ χ₃ : DirichletCharacter ℂ q}
    (h1 : χ₁ ^ 2 = 1) (h2 : χ₂ ^ 2 = 1) (h3 : χ₃ ^ 2 = 1) (h : χ₁ * χ₂ * χ₃ = 1) :
    χ₁ * χ₂ = χ₃ ∧ χ₁ * χ₃ = χ₂ ∧ χ₂ * χ₃ = χ₁ := by
  have i1 := inv_eq_self_of_sq_eq_one h1
  have i2 := inv_eq_self_of_sq_eq_one h2
  have key : ∀ x y z : DirichletCharacter ℂ q, x * y * z = 1 → y * z = x⁻¹ := by
    intro x y z hxyz
    have h1 : x * (y * z) = 1 := by rwa [mul_assoc] at hxyz
    exact eq_inv_of_mul_eq_one_right h1
  refine ⟨?_, ?_, ?_⟩
  · exact char_prod_pair_eq_third h2 h3 h
  · have h' : χ₂ * χ₁ * χ₃ = 1 := by rw [mul_comm χ₂ χ₁]; exact h
    rw [key χ₂ χ₁ χ₃ h', i2]
  · rw [key χ₁ χ₂ χ₃ h, i1]

/-- **Extraction at a fixed level**, with the two engine thresholds exposed. -/
theorem SigmaP3L_extract_at {a δ e : ℝ} (ha : 0 < a) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (he : 0 < e) :
    ∃ Lm Li : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
      (hreal : χ ^ 2 = 1) (ρ : ℂ) (lam1 lamχ τ : ℝ),
      2 ≤ q → Lm ≤ Real.log (q : ℝ) → Li ≤ Real.log (q : ℝ) →
      2 * a ≤ δ * Real.log (q : ℝ) →
      (∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N), N ≤ q → ψ ≠ 1 → ψ.IsPrimitive →
        ψ ^ 2 = 1 → Work.ZeroFreeTables.LogDerivHyp ψ δ (Real.log (q : ℝ)) (1 / 8 + e / 3)) →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 → |τ| ≤ 3 →
      ρ.re = 1 - lamχ / Real.log (q : ℝ) → 0 ≤ lam1 → lam1 ≤ 1 →
      (∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 →
        lam1 ≤ (1 - u.re) * Real.log (q : ℝ)) →
      Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) χ
        (((1 + a / Real.log (q : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I) a lam1
      ≤ -( Work.ZeroFreeTables.P3 ((a + lam1) / (((a + lamχ : ℝ) : ℂ)
              + (((τ - ρ.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + 8 * (a + lam1) / (δ * Real.log (q : ℝ)) + (a + lam1) * (1 / 8 + e) := by
  obtain ⟨Lm, hm⟩ := Work.ZeroFreeTables.P9.prim.masterP3 (a := a) (δ := δ)
    (c := 1 / 8 + e / 3) (e := e / 3) ha hδ0 hδ1 (by positivity) 1
  obtain ⟨Li, hi⟩ :=
    Work.ZeroFreeTables.XY.ImprimitiveSigmaReduce (a := a) (e := e / 3) ha (by positivity)
  refine ⟨Lm, Li, ?_⟩
  intro q _inst χ hχ hreal ρ lam1 lamχ τ hq2 hLm hLi h2aδ hfeed hρ hρim hτ hre hlam1
    hlam1le hmin
  have hLpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hconpos : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have hcondle : χ.conductor ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hlogN : Real.log ((χ.conductor : ℕ) : ℝ) ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by exact_mod_cast hconpos) (by exact_mod_cast hcondle)
  have hχ'ne : χ.primitiveCharacter ≠ 1 := by
    intro h1
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hχ'sq : χ.primitiveCharacter ^ 2 = 1 := by
    have hmap : (DirichletCharacter.changeLevel χ.conductor_dvd_level)
        (χ.primitiveCharacter ^ 2) = 1 := by
      rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, hreal]
    exact DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
      (by rw [hmap, DirichletCharacter.changeLevel_one])
  have hprim' : (χ.primitiveCharacter).IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hLD : Work.ZeroFreeTables.LogDerivHyp χ.primitiveCharacter δ (Real.log (q : ℝ))
      (1 / 8 + e / 3) :=
    hfeed χ.primitiveCharacter hcondle hχ'ne hprim' hχ'sq
  set s : ℂ := ((1 + a / Real.log (q : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I with hs
  have hsre : s.re = 1 + a / Real.log (q : ℝ) := by
    rw [hs]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  have hsim : |s.im| ≤ 3 := by
    have h : s.im = τ := by
      rw [hs]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    rw [h]; exact hτ
  have hlogqne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hLpos
  have hρle : lam1 ≤ lamχ := by
    have h := hmin ρ hρ (le_trans hρim (by norm_num))
    have hsimp : (1 - (1 - lamχ / Real.log (q : ℝ))) * Real.log (q : ℝ) = lamχ := by
      rw [sub_sub_cancel, div_mul_cancel₀ _ hlogqne]
    rw [hre] at h
    linarith only [h, hsimp]
  have hlamχnn : 0 ≤ lamχ := le_trans hlam1 hρle
  have hρim10 : |ρ.im| ≤ 10 := le_trans hρim (by norm_num)
  have hzero' : Work.LinnikContract.zeroMult χ.primitiveCharacter ρ ≠ 0 := by
    rw [Work.ZeroFreeTables.XY.zeroMult_primitiveCharacter_eq χ ρ]; exact hρ
  have hmin' : ∀ u : ℂ, Work.LinnikContract.zeroMult χ.primitiveCharacter u ≠ 0 →
      |u.im| ≤ 10 → lam1 ≤ (1 - u.re) * Real.log (q : ℝ) := by
    intro u hu him
    rw [Work.ZeroFreeTables.XY.zeroMult_primitiveCharacter_eq χ u] at hu
    exact hmin u hu him
  have hmaster : Work.ZeroFreeTables.SigmaP3L χ.conductor (Real.log (q : ℝ))
        χ.primitiveCharacter s a lam1
      ≤ -Work.ZeroFreeTables.P3NearSumL χ.conductor (Real.log (q : ℝ))
          χ.primitiveCharacter s a lam1 δ
        + (a + lam1) * (1 / 8 + e / 3 + e / 3) := by
    have h := hm χ.primitiveCharacter hχ'ne hprim' (L := Real.log (q : ℝ)) (lam₁ := lam1)
      hLm hlogN hlam1 hlam1le hLD s hsre (le_trans hsim (by norm_num))
    have heq : (a + lam1) * ((1 / 8 + e / 3) + e / 3) = (a + lam1) * (1 / 8 + e / 3 + e / 3) := by
      ring
    linarith only [h, heq, this]
  have hext := Work.ZeroFreeTables.P10.shifted_extract_of_point_bound (N := χ.conductor)
    χ.primitiveCharacter hχ'ne hprim' (a := a) (δ := δ) (c := 1 / 8 + e / 3) (e := e / 3)
    (lam1 := lam1) (lam := lamχ) (L := Real.log (q : ℝ)) (τ := τ)
    hδ0 hδ1 hLpos ha hlam1 hlamχnn h2aδ hτ hzero' hρim10 hre hmin' hmaster
  have himp := hi χ hχ hreal (L := Real.log (q : ℝ)) (lam₁ := lam1)
    hLi le_rfl hlam1 hlam1le s hsre hsim
  have hring : (a + lam1) * (1 / 8 + e / 3 + e / 3) + (a + lam1) * (e / 3)
      = (a + lam1) * (1 / 8 + e) := by ring
  linarith only [himp, hext, hring, _inst, this]

/-- **Extraction of a zero at its own point**, in the `P₃ℝ` form the weighted
combination consumes. -/
theorem SigmaP3L_extract_at_zero {a δ e : ℝ} (ha : 0 < a) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (he : 0 < e) :
    ∃ Lm Li : ℝ, ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
      (hreal : χ ^ 2 = 1) (ρ : ℂ) (lam1 lamχ : ℝ),
      2 ≤ q → Lm ≤ Real.log (q : ℝ) → Li ≤ Real.log (q : ℝ) →
      2 * a ≤ δ * Real.log (q : ℝ) →
      (∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N), N ≤ q → ψ ≠ 1 → ψ.IsPrimitive →
        ψ ^ 2 = 1 → Work.ZeroFreeTables.LogDerivHyp ψ δ (Real.log (q : ℝ)) (1 / 8 + e / 3)) →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 → |ρ.im| ≤ 1 →
      ρ.re = 1 - lamχ / Real.log (q : ℝ) → 0 ≤ lam1 → lam1 ≤ 1 →
      (∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ 10 →
        lam1 ≤ (1 - u.re) * Real.log (q : ℝ)) →
      Work.ZeroFreeTables.SigmaP3L q (Real.log (q : ℝ)) χ
        (((1 + a / Real.log (q : ℝ) : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I) a lam1
      ≤ -P3R ((a + lam1) / (a + lamχ))
        + 8 * (a + lam1) / (δ * Real.log (q : ℝ)) + (a + lam1) * (1 / 8 + e) := by
  obtain ⟨Lm, Li, h⟩ := SigmaP3L_extract_at (a := a) (δ := δ) (e := e) ha hδ0 hδ1 he
  refine ⟨Lm, Li, ?_⟩
  intro q _inst χ hχ hreal ρ lam1 lamχ hq2 hLm hLi h2a hfeed hρ hρim hre hlam1 hlam1le hmin
  have key := h χ hχ hreal ρ lam1 lamχ ρ.im hq2 hLm hLi h2a hfeed hρ hρim
    (le_trans hρim (by norm_num)) hre hlam1 hlam1le hmin
  have harg : (((ρ.im - ρ.im) * Real.log (q : ℝ) : ℝ) : ℂ) = 0 := by
    rw [sub_self, zero_mul, Complex.ofReal_zero]
  simp only [harg, zero_mul, add_zero] at key
  have hnum : ((a : ℂ) + (lam1 : ℂ)) = ((a + lam1 : ℝ) : ℂ) := by push_cast; ring
  rw [hnum] at key
  rw [P3_ofReal_div_eq_P3R] at key
  exact key

/-- The pole term at `s = 1 + a/L`, with the numerator of the `P₃`-argument in the
*pushed-in* form `↑a + ↑lam` produced by the providers' statements. -/
theorem P3_pole_eq_push {a lam L : ℝ} (ha : a ≠ 0) (hL : L ≠ 0) :
    (P3 (((a : ℂ) + (lam : ℂ)) / (((((1 + a / L : ℝ)) : ℂ) - 1) * (L : ℂ)))).re
      = P3R ((a + lam) / a) := by
  have h := P3_pole_eq (α := a + lam) ha hL
  have hnum : ((↑(a + lam) : ℂ)) = ((a : ℂ) + (lam : ℂ)) := by push_cast; ring
  rwa [hnum] at h

/-- The shifted pole term, with the numerator of the `P₃`-argument in the pushed-in
form on both sides. -/
theorem P3_pole_shift_eq_push {a lam L τ : ℝ} (hL : L ≠ 0) :
    (P3 (((a : ℂ) + (lam : ℂ)) / (((((1 + a / L : ℝ)) : ℂ) + (τ : ℂ) * Complex.I - 1)
          * (L : ℂ)))).re
      = (P3 (((a : ℂ) + (lam : ℂ)) / ((a : ℂ) + (((τ * L : ℝ)) : ℂ) * Complex.I))).re := by
  have h := P3_pole_shift_eq (α := a + lam) (a := a) (L := L) (τ := τ) hL
  have hnum : ((↑(a + lam) : ℂ)) = ((a : ℂ) + (lam : ℂ)) := by push_cast; ring
  rwa [hnum] at h

open scoped Classical BigOperators
open Work.ZeroFreeTables.P10
open Work.ZeroFreeTables.P3 (tsum_finset_lincomb)

/-! ## 14e. The fourteen-term combination, locally re-assembled

`P10/case3_weighted_combination.lean` proves the same two facts, but its module imports
`P10/comb14Raw_nonneg.lean`, whose single declaration is a placeholder.  The engine
therefore re-runs here the (short) linearisation `S14 = L⁻¹ ∑ₙ comb14Raw n` and the
weighted-combination arithmetic, *taking the pointwise positivity of `comb14Raw` as a
hypothesis* (proved separately in `HB103/Comb14Positivity.lean`). -/

/-- Summability of `hbRawG` at the point `σ + iΔ`. -/
theorem summable_hbRawG_engine {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {σ : ℝ}
    (hσ : 1 < σ) (L : ℝ) (hL : 0 < L) (Δ a lam₁ : ℝ) :
    Summable (hbRawG N χ L ((σ : ℂ) + (Δ : ℂ) * Complex.I) a lam₁) :=
  (summable_hbTermG χ hσ L hL Δ a lam₁).congr
    (fun n => (hbRawG_eq_hbTermG χ L σ Δ a lam₁ n).symm)

/-- **Linearisation.**  `S14` is `L⁻¹` times the absolutely convergent series of the fourteen
`hbRawG` summands. -/
theorem S14_eq_engine (N : ℕ) [NeZero N] (chi1 chi2 chi3 : DirichletCharacter ℂ N)
    (L σ γ1 γ2 γ3 a lam₁ : ℝ) (hσ : 1 < σ) (hL : 0 < L) :
    S14 N chi1 chi2 chi3 L σ γ1 γ2 γ3 a lam₁
      = L⁻¹ * ∑' n, comb14Raw N chi1 chi2 chi3 L σ γ1 γ2 γ3 a lam₁ n := by
  have hsumm : ∀ i : Fin 14, Summable (hbRawG N (chi14 N chi1 chi2 chi3 i) L
      ((σ : ℂ) + ((dl14 γ1 γ2 γ3 i : ℝ) : ℂ) * Complex.I) a lam₁) :=
    fun i => summable_hbRawG_engine _ hσ L hL _ a lam₁
  calc ∑ i : Fin 14, coef14 i * SigmaP3L N L (chi14 N chi1 chi2 chi3 i)
          ((σ : ℂ) + ((dl14 γ1 γ2 γ3 i : ℝ) : ℂ) * Complex.I) a lam₁
      = ∑ i : Fin 14, coef14 i * (L⁻¹ * ∑' n, hbRawG N (chi14 N chi1 chi2 chi3 i) L
          ((σ : ℂ) + ((dl14 γ1 γ2 γ3 i : ℝ) : ℂ) * Complex.I) a lam₁ n) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [SigmaP3L_eq_hbRawG]
      _ = L⁻¹ * ∑ i : Fin 14, coef14 i * (∑' n, hbRawG N (chi14 N chi1 chi2 chi3 i) L
          ((σ : ℂ) + ((dl14 γ1 γ2 γ3 i : ℝ) : ℂ) * Complex.I) a lam₁ n) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = L⁻¹ * (∑' n, ∑ i : Fin 14, coef14 i * hbRawG N (chi14 N chi1 chi2 chi3 i) L
          ((σ : ℂ) + ((dl14 γ1 γ2 γ3 i : ℝ) : ℂ) * Complex.I) a lam₁ n) := by
        congr 1
        exact tsum_finset_lincomb Finset.univ _ coef14 (fun i _ => hsumm i)
      _ = L⁻¹ * ∑' n, comb14Raw N chi1 chi2 chi3 L σ γ1 γ2 γ3 a lam₁ n := rfl

/-- **`S14 ≥ 0`**, from the pointwise positivity of `comb14Raw`. -/
theorem S14_nonneg_engine {N : ℕ} [NeZero N] (chi1 chi2 chi3 : DirichletCharacter ℂ N)
    (L σ γ1 γ2 γ3 a lam1 : ℝ) (hL : 0 < L) (hσ : 1 < σ)
    (hpos : ∀ n : ℕ, 0 ≤ comb14Raw N chi1 chi2 chi3 L σ γ1 γ2 γ3 a lam1 n) :
    0 ≤ S14 N chi1 chi2 chi3 L σ γ1 γ2 γ3 a lam1 := by
  rw [S14_eq_engine N chi1 chi2 chi3 L σ γ1 γ2 γ3 a lam1 hσ hL]
  exact mul_nonneg (inv_nonneg.mpr hL.le) (tsum_nonneg (fun n => hpos n))

/-- The weighted combination of the fourteen `Σ`-bounds, with the pointwise positivity of
`comb14Raw` as a hypothesis.  (Copy of `case3_weighted_combination`, locally re-assembled so
that the engine does not inherit the placeholder of `P10/comb14Raw_nonneg.lean`.) -/
theorem case3_weighted_combination_engine {N : ℕ} [NeZero N]
    (chi1 chi2 chi3 : DirichletCharacter ℂ N) (rho1 rho2 rho3 : ℂ)
    {a lam1 lam2 lam3 δ L e1 e2 e3 eP eS eps : ℝ}
    (hpos0 : ∀ n : ℕ, 0 ≤ comb14Raw N chi1 chi2 chi3 L (1 + a / L) rho1.im rho2.im rho3.im
      a lam1 n)
    (ha : 0 < a) (hδ : 0 < δ) (hδ1 : δ < 1) (hL : 0 < L)
    (hlam1 : 0 ≤ lam1) (h12 : lam1 ≤ lam2) (h13 : lam1 ≤ lam3)
    (heP : 0 ≤ eP) (heS : 0 ≤ eS) (hsum : e1 + e2 + e3 + eP + eS + 24 / (δ * L) ≤ eps)
    (hsq1 : chi1 ^ 2 = 1) (hsq2 : chi2 ^ 2 = 1) (hsq3 : chi3 ^ 2 = 1)
    (hprod : chi1 * chi2 * chi3 = 1)
    (hb1 : Work.ZeroFreeTables.SigmaP3L N L chi1
        (((1 + a / L : ℝ) : ℂ) + (rho1.im : ℂ) * Complex.I) a lam1
      ≤ -P3R ((a + lam1) / (a + lam1)) + 8 * (a + lam1) / (δ * L) + (a + lam1) * (1 / 8 + e1))
    (hb2 : Work.ZeroFreeTables.SigmaP3L N L chi2
        (((1 + a / L : ℝ) : ℂ) + (rho2.im : ℂ) * Complex.I) a lam1
      ≤ -P3R ((a + lam1) / (a + lam2)) + 8 * (a + lam1) / (δ * L) + (a + lam1) * (1 / 8 + e2))
    (hb3 : Work.ZeroFreeTables.SigmaP3L N L chi3
        (((1 + a / L : ℝ) : ℂ) + (rho3.im : ℂ) * Complex.I) a lam1
      ≤ -P3R ((a + lam1) / (a + lam3)) + 8 * (a + lam1) / (δ * L) + (a + lam1) * (1 / 8 + e3))
    (hpole : Work.ZeroFreeTables.SigmaP3L N L 1 ((1 + a / L : ℝ) : ℂ) a lam1
      ≤ P3R ((a + lam1) / a) + (a + lam1) * (0 + eP))
    (hPstar : (1 / 2) * (Work.ZeroFreeTables.SigmaP3L N L (chi1 * chi2)
            (((1 + a / L : ℝ) : ℂ) + ((rho1.im + rho2.im : ℝ) : ℂ) * Complex.I) a lam1
        + Work.ZeroFreeTables.SigmaP3L N L (chi1 * chi2⁻¹)
            (((1 + a / L : ℝ) : ℂ) + ((rho1.im - rho2.im : ℝ) : ℂ) * Complex.I) a lam1
        + Work.ZeroFreeTables.SigmaP3L N L (chi1 * chi3)
            (((1 + a / L : ℝ) : ℂ) + ((rho1.im + rho3.im : ℝ) : ℂ) * Complex.I) a lam1
        + Work.ZeroFreeTables.SigmaP3L N L (chi1 * chi3⁻¹)
            (((1 + a / L : ℝ) : ℂ) + ((rho1.im - rho3.im : ℝ) : ℂ) * Complex.I) a lam1
        + Work.ZeroFreeTables.SigmaP3L N L (chi2 * chi3)
            (((1 + a / L : ℝ) : ℂ) + ((rho2.im + rho3.im : ℝ) : ℂ) * Complex.I) a lam1
        + Work.ZeroFreeTables.SigmaP3L N L (chi2 * chi3⁻¹)
            (((1 + a / L : ℝ) : ℂ) + ((rho2.im - rho3.im : ℝ) : ℂ) * Complex.I) a lam1)
      + (1 / 4) * (Work.ZeroFreeTables.SigmaP3L N L 1
            (((1 + a / L : ℝ) : ℂ) + ((rho1.im + rho2.im + rho3.im : ℝ) : ℂ) * Complex.I) a lam1
        + Work.ZeroFreeTables.SigmaP3L N L 1
            (((1 + a / L : ℝ) : ℂ) + ((rho1.im + rho2.im - rho3.im : ℝ) : ℂ) * Complex.I) a lam1
        + Work.ZeroFreeTables.SigmaP3L N L 1
            (((1 + a / L : ℝ) : ℂ) + ((rho1.im - rho2.im + rho3.im : ℝ) : ℂ) * Complex.I) a lam1
        + Work.ZeroFreeTables.SigmaP3L N L 1
            (((1 + a / L : ℝ) : ℂ) + ((-rho1.im + rho2.im + rho3.im : ℝ) : ℂ) * Complex.I) a lam1)
      ≤ (a + lam1) * (3 / 8 + eS)) :
    P3R 1 + P3R ((a + lam1) / (a + lam2)) + P3R ((a + lam1) / (a + lam3))
      ≤ P3R ((a + lam1) / a) + (a + lam1) * (3 / 4 + eps) := by
  have hα : (0:ℝ) < a + lam1 := by linarith only [ha, hlam1]
  have hσ : (1:ℝ) < 1 + a / L := by
    have : 0 < a / L := div_pos ha hL
    linarith only [this]
  have hpos : 0 ≤ S14 N chi1 chi2 chi3 L (1 + a / L) rho1.im rho2.im rho3.im a lam1 :=
    S14_nonneg_engine chi1 chi2 chi3 L (1 + a / L) rho1.im rho2.im rho3.im a lam1 hL hσ hpos0
  set P : ℝ := SigmaP3L N L 1 ((1 + a / L : ℝ) : ℂ) a lam1 with hPdef
  set C1 : ℝ := SigmaP3L N L chi1 (((1 + a / L : ℝ) : ℂ) + (rho1.im : ℂ) * Complex.I) a lam1
    with hC1def
  set C2 : ℝ := SigmaP3L N L chi2 (((1 + a / L : ℝ) : ℂ) + (rho2.im : ℂ) * Complex.I) a lam1
    with hC2def
  set C3 : ℝ := SigmaP3L N L chi3 (((1 + a / L : ℝ) : ℂ) + (rho3.im : ℂ) * Complex.I) a lam1
    with hC3def
  have hP1 : P3R ((a + lam1) / (a + lam1)) = P3R 1 := by rw [div_self (ne_of_gt hα)]
  rw [hP1] at hb1
  rw [S14_unfold] at hpos
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hpos
  rw [← hPdef] at hpos
  rw [← hC1def] at hpos
  rw [← hC2def] at hpos
  rw [← hC3def] at hpos
  have h1 : P3R 1 ≤ -C1 + 8 * (a + lam1) / (δ * L) + (a + lam1) * (1 / 8 + e1) := by linarith only [hb1]
  have h2 : P3R ((a + lam1) / (a + lam2))
      ≤ -C2 + 8 * (a + lam1) / (δ * L) + (a + lam1) * (1 / 8 + e2) := by linarith only [hb2]
  have h3 : P3R ((a + lam1) / (a + lam3))
      ≤ -C3 + 8 * (a + lam1) / (δ * L) + (a + lam1) * (1 / 8 + e3) := by linarith only [hb3]
  have h4 : -P3R ((a + lam1) / a) ≤ -P + (a + lam1) * (0 + eP) := by linarith only [hpole]
  have hAB : P3R 1 + P3R ((a + lam1) / (a + lam2)) + P3R ((a + lam1) / (a + lam3))
      - P3R ((a + lam1) / a)
      ≤ (a + lam1) * (3 / 8 + eS) + 3 * (8 * (a + lam1) / (δ * L))
        + ((a + lam1) * (1 / 8 + e1) + (a + lam1) * (1 / 8 + e2) + (a + lam1) * (1 / 8 + e3)
            + (a + lam1) * (0 + eP)) := by
    linarith [hpos, hPstar, h1, h2, h3, h4]
  have hX : (3:ℝ) / 8 + eS + (24 / (δ * L) + (3 / 8 + e1 + e2 + e3 + eP)) ≤ 3 / 4 + eps := by
    linarith only [hsum]
  have hfin : P3R 1 + P3R ((a + lam1) / (a + lam2)) + P3R ((a + lam1) / (a + lam3))
      - P3R ((a + lam1) / a) ≤ (a + lam1) * (3 / 4 + eps) := by
    calc P3R 1 + P3R ((a + lam1) / (a + lam2)) + P3R ((a + lam1) / (a + lam3))
        - P3R ((a + lam1) / a)
        ≤ (a + lam1) * (3 / 8 + eS) + 3 * (8 * (a + lam1) / (δ * L))
          + ((a + lam1) * (1 / 8 + e1) + (a + lam1) * (1 / 8 + e2)
              + (a + lam1) * (1 / 8 + e3) + (a + lam1) * (0 + eP)) := hAB
      _ = (a + lam1) * ((3 / 8 + eS) + (24 / (δ * L) + (3 / 8 + e1 + e2 + e3 + eP))) := by ring
      _ ≤ (a + lam1) * (3 / 4 + eps) := mul_le_mul_of_nonneg_left hX hα.le
  linarith only [hfin]

set_option maxHeartbeats 4000000 in
theorem HBLemma10_3_engine_proof : Work.ZeroFreeTables.HBLemma10_3_engine := by

  intro ε hε
  -- the two budgets
  set e1 : ℝ := ε / 100 with he1def
  have he1pos : 0 < e1 := by rw [he1def]; linarith only [hε]
  have he13pos : 0 < e1 / 3 := by linarith only [he1pos]
  -- HB Lemma 3.1 at `φ = 1/4` with `e = e1/3` (so `1/8 + e = 1/8 + e1` after the
  -- three internal losses of the extraction)
  obtain ⟨L0, δ, hδ0, hδ1, hfeed0⟩ :=
    Work.ZeroFreeTables.HB95h2.logDerivEighth (e := e1 / 3) he13pos
  -- the extraction, with the two engine thresholds
  obtain ⟨Lm, Li, hpair⟩ :=
    SigmaP3L_extract_at (a := 18/7) (δ := δ) (e := e1) (by norm_num) hδ0 hδ1 he1pos
  obtain ⟨Lz, Lzi, hsingle⟩ :=
    SigmaP3L_extract_at_zero (a := 18/7) (δ := δ) (e := e1) (by norm_num) hδ0 hδ1 he1pos
  -- the principal-character bound
  obtain ⟨qP, hP⟩ := Work.P10.PrincipalSigmaBound_18_7 (6/7) e1 (by norm_num) he1pos
  -- the joint threshold: `log q` dominates everything, and `48/(δ log q) ≤ ε/10`
  set Lthr : ℝ := max (max L0 (max Lm Lz))
    (max (max Li Lzi) (max (48 / (δ * (ε / 10))) (2 * (18 / 7) / δ))) with hLthr
  refine ⟨max 2 (max qP (Nat.ceil (Real.exp Lthr) + 1)), ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hm hsq1 hsq2 hsq3 hprod hρ₁im hz₂ hχ₂a hχ₂b hz₃
    hχ₃a hχ₃b hχ₃c hχ₃d _hminW₁ _hminW₂ _hminW₃ hlam2le3 hlam3pos hlam3le
  have hq2 : 2 ≤ q := le_trans (le_max_left 2 (max qP (Nat.ceil (Real.exp Lthr) + 1))) hq
  have hqP : qP ≤ q := le_trans (le_trans (le_max_left qP (Nat.ceil (Real.exp Lthr) + 1))
      (le_max_right 2 (max qP (Nat.ceil (Real.exp Lthr) + 1)))) hq
  have hqE : Nat.ceil (Real.exp Lthr) + 1 ≤ q := le_trans (le_trans
      (le_max_right qP (Nat.ceil (Real.exp Lthr) + 1))
      (le_max_right 2 (max qP (Nat.ceil (Real.exp Lthr) + 1)))) hq
  have hLthrle : Lthr ≤ Real.log (q : ℝ) := by
    have hexp : Real.exp Lthr ≤ (q : ℝ) := by
      have h1 : Real.exp Lthr ≤ ((Nat.ceil (Real.exp Lthr) : ℕ) : ℝ) := Nat.le_ceil _
      have h2 : ((Nat.ceil (Real.exp Lthr) : ℕ) : ℝ) ≤ (q : ℝ) := by
        have h3 : Nat.ceil (Real.exp Lthr) ≤ q := by omega
        exact_mod_cast h3
      linarith only [h1, h2]
    have h := Real.log_le_log (Real.exp_pos Lthr) hexp
    rwa [Real.log_exp] at h
  have hcopy := hLthrle
  rw [hLthr] at hcopy
  have hA : max L0 (max Lm Lz) ≤ Real.log (q : ℝ) :=
    le_trans (le_max_left (max L0 (max Lm Lz))
      (max (max Li Lzi) (max (48 / (δ * (ε / 10))) (2 * (18 / 7) / δ)))) hcopy
  have hB : max (max Li Lzi) (max (48 / (δ * (ε / 10))) (2 * (18 / 7) / δ))
      ≤ Real.log (q : ℝ) :=
    le_trans (le_max_right (max L0 (max Lm Lz))
      (max (max Li Lzi) (max (48 / (δ * (ε / 10))) (2 * (18 / 7) / δ)))) hcopy
  have hL0 : L0 ≤ Real.log (q : ℝ) := le_trans (le_max_left L0 (max Lm Lz)) hA
  have hLm : Lm ≤ Real.log (q : ℝ) :=
    le_trans (le_trans (le_max_left Lm Lz) (le_max_right L0 (max Lm Lz))) hA
  have hLz : Lz ≤ Real.log (q : ℝ) :=
    le_trans (le_trans (le_max_right Lm Lz) (le_max_right L0 (max Lm Lz))) hA
  have hLi : Li ≤ Real.log (q : ℝ) :=
    le_trans (le_trans (le_max_left Li Lzi)
      (le_max_left (max Li Lzi) (max (48 / (δ * (ε / 10))) (2 * (18 / 7) / δ)))) hB
  have hLzi : Lzi ≤ Real.log (q : ℝ) :=
    le_trans (le_trans (le_max_right Li Lzi)
      (le_max_left (max Li Lzi) (max (48 / (δ * (ε / 10))) (2 * (18 / 7) / δ)))) hB
  have hD : 48 / (δ * (ε / 10)) ≤ Real.log (q : ℝ) :=
    le_trans (le_trans (le_max_left (48 / (δ * (ε / 10))) (2 * (18 / 7) / δ))
      (le_max_right (max Li Lzi) (max (48 / (δ * (ε / 10))) (2 * (18 / 7) / δ)))) hB
  have h2a : 2 * (18 / 7) / δ ≤ Real.log (q : ℝ) :=
    le_trans (le_trans (le_max_right (48 / (δ * (ε / 10))) (2 * (18 / 7) / δ))
      (le_max_right (max Li Lzi) (max (48 / (δ * (ε / 10))) (2 * (18 / 7) / δ)))) hB
  have hLpos : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hLne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hLpos
  have h2aδ : 2 * (18 / 7 : ℝ) ≤ δ * Real.log (q : ℝ) := by
    have h := (div_le_iff₀ hδ0).mp h2a
    rw [mul_comm (Real.log (q : ℝ)) δ] at h
    exact h
  have hbud : 48 / (δ * Real.log (q : ℝ)) ≤ ε / 10 := by
    have h' : 48 ≤ Real.log (q : ℝ) * (δ * (ε / 10)) :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < δ * (ε / 10))).mp hD
    rw [div_le_iff₀ (mul_pos hδ0 hLpos)]
    linarith only [h']
  -- ### the setting: the three `λ`'s
  set lam1 : ℝ := lamOf q ρ₁ with hlam1def
  set lam2 : ℝ := lamOf q ρ₂ with hlam2def
  set lam3 : ℝ := lamOf q ρ₃ with hlam3def
  have hz₁ : IsZ χ₁ ρ₁ := hm.1.1
  have hlam10 : 0 ≤ lam1 := by rw [hlam1def]; exact lamOf_nonneg_of_isZ_103 hq2 hz₁
  have hlam20 : 0 ≤ lam2 := by rw [hlam2def]; exact lamOf_nonneg_of_isZ_103 hq2 hz₂
  have hlam30 : 0 ≤ lam3 := by rw [hlam3def]; exact lamOf_nonneg_of_isZ_103 hq2 hz₃
  have hlam12 : lam1 ≤ lam2 := by
    rw [hlam1def, hlam2def]; exact lamOf_le_of_isMin1Wide hm hz₂
  have hlam23 : lam2 ≤ lam3 := by rw [hlam2def, hlam3def]; exact hlam2le3
  have hlam13 : lam1 ≤ lam3 := le_trans hlam12 hlam23
  have hlam367 : lam3 ≤ 6 / 7 := by rw [hlam3def]; exact hlam3le
  have hlam267 : lam2 ≤ 6 / 7 := le_trans hlam23 hlam367
  have hlam167 : lam1 ≤ 6 / 7 := le_trans hlam13 hlam367
  have hlam11 : lam1 ≤ 1 := le_trans hlam167 (by norm_num)
  have hlam3pos' : 0 < lam3 := by rw [hlam3def]; exact hlam3pos
  -- the real parts at the zeros
  have hρre1 : ρ₁.re = 1 - lam1 / Real.log (q : ℝ) := by
    rw [hlam1def, lamOf]; field_simp [hLne]; ring
  have hρre2 : ρ₂.re = 1 - lam2 / Real.log (q : ℝ) := by
    rw [hlam2def, lamOf]; field_simp [hLne]; ring
  have hρre3 : ρ₃.re = 1 - lam3 / Real.log (q : ℝ) := by
    rw [hlam3def, lamOf]; field_simp [hLne]; ring
  -- the minimality windows (`IsMin1WideAt 10` sees all three characters)
  have hmin₁ : ∀ u : ℂ, zeroMult χ₁ u ≠ 0 → |u.im| ≤ 10 →
      lam1 ≤ (1 - u.re) * Real.log (q : ℝ) := by
    intro u hu him
    rw [hlam1def]
    exact hm.2 χ₁ u hz₁.1 hu him
  have hmin₂ : ∀ u : ℂ, zeroMult χ₂ u ≠ 0 → |u.im| ≤ 10 →
      lam1 ≤ (1 - u.re) * Real.log (q : ℝ) := by
    intro u hu him
    rw [hlam1def]
    exact hm.2 χ₂ u hz₂.1 hu him
  have hmin₃ : ∀ u : ℂ, zeroMult χ₃ u ≠ 0 → |u.im| ≤ 10 →
      lam1 ≤ (1 - u.re) * Real.log (q : ℝ) := by
    intro u hu him
    rw [hlam1def]
    exact hm.2 χ₃ u hz₃.1 hu him
  -- the HB Lemma 3.1 feed at the single scale `log q`
  have hfeed : ∀ {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N), N ≤ q → ψ ≠ 1 →
      ψ.IsPrimitive → ψ ^ 2 = 1 →
      Work.ZeroFreeTables.LogDerivHyp ψ δ (Real.log (q : ℝ)) (1 / 8 + e1 / 3) := by
    intro N _iN ψ hN h1 h2 h3
    have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
    have hlogN : Real.log (N : ℝ) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by exact_mod_cast hNpos) (by exact_mod_cast hN)
    exact hfeed0 ψ h1 h2 h3 hL0 hlogN
  -- the abbreviations used by the nine Σ-bounds
  have hσ : (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ)) = (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ)) := rfl
  -- ### the three single extractions
  have hb1 : SigmaP3L q (Real.log (q : ℝ)) χ₁
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (ρ₁.im : ℂ) * Complex.I) (18 / 7) lam1
      ≤ -P3R (((18 / 7 : ℝ) + lam1) / ((18 / 7 : ℝ) + lam1))
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) :=
    hsingle χ₁ hz₁.1 hsq1 ρ₁ lam1 lam1 hq2 hLz hLzi h2aδ hfeed hz₁.2.1 hz₁.2.2 hρre1
      hlam10 hlam11 hmin₁
  have hb2 : SigmaP3L q (Real.log (q : ℝ)) χ₂
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (ρ₂.im : ℂ) * Complex.I) (18 / 7) lam1
      ≤ -P3R (((18 / 7 : ℝ) + lam1) / ((18 / 7 : ℝ) + lam2))
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) :=
    hsingle χ₂ hz₂.1 hsq2 ρ₂ lam1 lam2 hq2 hLz hLzi h2aδ hfeed hz₂.2.1 hz₂.2.2 hρre2
      hlam10 hlam11 hmin₂
  have hb3 : SigmaP3L q (Real.log (q : ℝ)) χ₃
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (ρ₃.im : ℂ) * Complex.I) (18 / 7) lam1
      ≤ -P3R (((18 / 7 : ℝ) + lam1) / ((18 / 7 : ℝ) + lam3))
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) :=
    hsingle χ₃ hz₃.1 hsq3 ρ₃ lam1 lam3 hq2 hLz hLzi h2aδ hfeed hz₃.2.1 hz₃.2.2 hρre3
      hlam10 hlam11 hmin₃
  -- ### the six pair extractions
  have hτa : |ρ₁.im + ρ₂.im| ≤ 3 := by
    have h := abs_add_le ρ₁.im ρ₂.im
    linarith only [h, hz₁.2.2, hz₂.2.2, hδ0, hδ1, _inst, hz₁, hz₂]
  have hp1 : SigmaP3L q (Real.log (q : ℝ)) (χ₁ * χ₂)
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₁.im + ρ₂.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ -(P3 (((18 / 7 : ℝ) + lam1) / ((((18 / 7 : ℝ) + lam3 : ℝ) : ℂ)
            + (((ρ₂.im - ρ₃.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) := by
    have h := hpair χ₃ hz₃.1 hsq3 ρ₃ lam1 lam3 (ρ₁.im + ρ₂.im) hq2 hLm hLi h2aδ hfeed
      hz₃.2.1 hz₃.2.2 hτa hρre3 hlam10 hlam11 hmin₃
    have harg : ((ρ₁.im + ρ₂.im) - ρ₃.im) * Real.log (q : ℝ)
        = (ρ₂.im - ρ₃.im) * Real.log (q : ℝ) := by
      rw [hρ₁im]; ring
    rw [harg] at h
    rw [← (char_pair_prod_eq_third hsq1 hsq2 hsq3 hprod).1] at h
    exact h
  have hτb : |ρ₁.im - ρ₂.im| ≤ 3 := by
    have h1 := abs_le.mp hz₁.2.2
    have h2 := abs_le.mp hz₂.2.2
    rw [abs_le]; constructor <;> linarith only [hδ0, hδ1, hρ₁im, h2]
  have hp2 : SigmaP3L q (Real.log (q : ℝ)) (χ₁ * χ₂⁻¹)
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₁.im - ρ₂.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ -(P3 (((18 / 7 : ℝ) + lam1) / ((((18 / 7 : ℝ) + lam3 : ℝ) : ℂ)
            + (((-(ρ₂.im + ρ₃.im)) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) := by
    have h := hpair χ₃ hz₃.1 hsq3 ρ₃ lam1 lam3 (ρ₁.im - ρ₂.im) hq2 hLm hLi h2aδ hfeed
      hz₃.2.1 hz₃.2.2 hτb hρre3 hlam10 hlam11 hmin₃
    have harg : ((ρ₁.im - ρ₂.im) - ρ₃.im) * Real.log (q : ℝ)
        = (-(ρ₂.im + ρ₃.im)) * Real.log (q : ℝ) := by
      rw [hρ₁im]; ring
    rw [harg] at h
    have hchar : χ₁ * χ₂⁻¹ = χ₃ := by
      rw [inv_eq_self_of_sq_eq_one hsq2]
      exact (char_pair_prod_eq_third hsq1 hsq2 hsq3 hprod).1
    rw [← hchar] at h
    exact h
  have hτc : |ρ₁.im + ρ₃.im| ≤ 3 := by
    have h := abs_add_le ρ₁.im ρ₃.im
    linarith only [h, hz₁.2.2, hz₃.2.2, hδ0, hδ1, _inst, hz₁, hz₃]
  have hp3 : SigmaP3L q (Real.log (q : ℝ)) (χ₁ * χ₃)
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₁.im + ρ₃.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ -(P3 (((18 / 7 : ℝ) + lam1) / ((((18 / 7 : ℝ) + lam2 : ℝ) : ℂ)
            + (((ρ₃.im - ρ₂.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) := by
    have h := hpair χ₂ hz₂.1 hsq2 ρ₂ lam1 lam2 (ρ₁.im + ρ₃.im) hq2 hLm hLi h2aδ hfeed
      hz₂.2.1 hz₂.2.2 hτc hρre2 hlam10 hlam11 hmin₂
    have harg : ((ρ₁.im + ρ₃.im) - ρ₂.im) * Real.log (q : ℝ)
        = (ρ₃.im - ρ₂.im) * Real.log (q : ℝ) := by
      rw [hρ₁im]; ring
    rw [harg] at h
    rw [← (char_pair_prod_eq_third hsq1 hsq2 hsq3 hprod).2.1] at h
    exact h
  have hτd : |ρ₁.im - ρ₃.im| ≤ 3 := by
    have h1 := abs_le.mp hz₁.2.2
    have h2 := abs_le.mp hz₃.2.2
    rw [abs_le]; constructor <;> linarith only [hδ0, hδ1, hρ₁im, h2]
  have hp4 : SigmaP3L q (Real.log (q : ℝ)) (χ₁ * χ₃⁻¹)
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₁.im - ρ₃.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ -(P3 (((18 / 7 : ℝ) + lam1) / ((((18 / 7 : ℝ) + lam2 : ℝ) : ℂ)
            + (((-(ρ₂.im + ρ₃.im)) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) := by
    have h := hpair χ₂ hz₂.1 hsq2 ρ₂ lam1 lam2 (ρ₁.im - ρ₃.im) hq2 hLm hLi h2aδ hfeed
      hz₂.2.1 hz₂.2.2 hτd hρre2 hlam10 hlam11 hmin₂
    have harg : ((ρ₁.im - ρ₃.im) - ρ₂.im) * Real.log (q : ℝ)
        = (-(ρ₂.im + ρ₃.im)) * Real.log (q : ℝ) := by
      rw [hρ₁im]; ring
    rw [harg] at h
    have hchar : χ₁ * χ₃⁻¹ = χ₂ := by
      rw [inv_eq_self_of_sq_eq_one hsq3]
      exact (char_pair_prod_eq_third hsq1 hsq2 hsq3 hprod).2.1
    rw [← hchar] at h
    exact h
  have hτe : |ρ₂.im + ρ₃.im| ≤ 3 := by
    have h := abs_add_le ρ₂.im ρ₃.im
    linarith only [h, hz₂.2.2, hz₃.2.2, hδ0, hδ1, _inst, hz₂, hz₃]
  have hp5 : SigmaP3L q (Real.log (q : ℝ)) (χ₂ * χ₃)
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₂.im + ρ₃.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ -(P3 (((18 / 7 : ℝ) + lam1) / ((((18 / 7 : ℝ) + lam1 : ℝ) : ℂ)
            + (((ρ₂.im + ρ₃.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) := by
    have h := hpair χ₁ hz₁.1 hsq1 ρ₁ lam1 lam1 (ρ₂.im + ρ₃.im) hq2 hLm hLi h2aδ hfeed
      hz₁.2.1 hz₁.2.2 hτe hρre1 hlam10 hlam11 hmin₁
    have harg : ((ρ₂.im + ρ₃.im) - ρ₁.im) * Real.log (q : ℝ)
        = (ρ₂.im + ρ₃.im) * Real.log (q : ℝ) := by
      rw [hρ₁im]; ring
    rw [harg] at h
    rw [← (char_pair_prod_eq_third hsq1 hsq2 hsq3 hprod).2.2] at h
    exact h
  have hτf : |ρ₂.im - ρ₃.im| ≤ 3 := by
    have h1 := abs_le.mp hz₂.2.2
    have h2 := abs_le.mp hz₃.2.2
    rw [abs_le]; constructor <;> linarith only [hδ0, hδ1, h1, h2]
  have hp6 : SigmaP3L q (Real.log (q : ℝ)) (χ₂ * χ₃⁻¹)
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₂.im - ρ₃.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ -(P3 (((18 / 7 : ℝ) + lam1) / ((((18 / 7 : ℝ) + lam1 : ℝ) : ℂ)
            + (((ρ₂.im - ρ₃.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + 8 * ((18 / 7 : ℝ) + lam1) / (δ * Real.log (q : ℝ))
        + ((18 / 7 : ℝ) + lam1) * (1 / 8 + e1) := by
    have h := hpair χ₁ hz₁.1 hsq1 ρ₁ lam1 lam1 (ρ₂.im - ρ₃.im) hq2 hLm hLi h2aδ hfeed
      hz₁.2.1 hz₁.2.2 hτf hρre1 hlam10 hlam11 hmin₁
    have harg : ((ρ₂.im - ρ₃.im) - ρ₁.im) * Real.log (q : ℝ)
        = (ρ₂.im - ρ₃.im) * Real.log (q : ℝ) := by
      rw [hρ₁im]; ring
    rw [harg] at h
    have hchar : χ₂ * χ₃⁻¹ = χ₁ := by
      rw [inv_eq_self_of_sq_eq_one hsq3]
      exact (char_pair_prod_eq_third hsq1 hsq2 hsq3 hprod).2.2
    rw [← hchar] at h
    exact h
  -- ### the five principal-character bounds
  have hpole : SigmaP3L q (Real.log (q : ℝ)) 1
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ)) (18 / 7) lam1
      ≤ P3R (((18 / 7 : ℝ) + lam1) / (18 / 7)) + ((18 / 7 : ℝ) + lam1) * (0 + e1) := by
    have hsre : (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ)).re
        = 1 + (18 / 7) / Real.log (q : ℝ) := Complex.ofReal_re _
    have hsim : |(((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ)).im| ≤ 4 := by
      simp only [Complex.ofReal_im, abs_zero]; norm_num
    have h := hP q hqP lam1 (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ)) hlam10 hlam167 hsre hsim
    rw [P3_pole_eq_push (a := (18 / 7 : ℝ)) (lam := lam1) (L := Real.log (q : ℝ))
      (by norm_num) hLne] at h
    simpa [zero_add] using h
  have hprinc : ∀ τ : ℝ, |τ| ≤ 4 →
      SigmaP3L q (Real.log (q : ℝ)) 1
        (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I) (18 / 7) lam1
      ≤ (P3 (((18 / 7 : ℝ) + lam1) / (((18 / 7 : ℝ) : ℂ)
            + (((τ * Real.log (q : ℝ) : ℝ)) : ℂ) * Complex.I))).re
        + ((18 / 7 : ℝ) + lam1) * e1 := by
    intro τ hτ
    have hsre : (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I).re
        = 1 + (18 / 7) / Real.log (q : ℝ) := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    have hsim : |(((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I).im| ≤ 4 := by
      have h2 : (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I).im = τ := by
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
      rw [h2]; exact hτ
    have h := hP q hqP lam1
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + (τ : ℂ) * Complex.I) hlam10 hlam167 hsre hsim
    rw [P3_pole_shift_eq_push (a := (18 / 7 : ℝ)) (lam := lam1) (L := Real.log (q : ℝ))
      (τ := τ) hLne] at h
    exact h
  have hq1 : SigmaP3L q (Real.log (q : ℝ)) 1
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₁.im + ρ₂.im + ρ₃.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ (P3 (((18 / 7 : ℝ) + lam1) / (((18 / 7 : ℝ) : ℂ)
            + (((ρ₂.im + ρ₃.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + ((18 / 7 : ℝ) + lam1) * (0 + e1) := by
    have hpt : ((ρ₁.im + ρ₂.im + ρ₃.im : ℝ) : ℂ) = ((ρ₂.im + ρ₃.im : ℝ) : ℂ) := by
      have h1 : ρ₁.im + ρ₂.im + ρ₃.im = ρ₂.im + ρ₃.im := by rw [hρ₁im]; ring
      rw [h1]
    rw [hpt]
    have hτ : |ρ₂.im + ρ₃.im| ≤ 4 := by
      have h := abs_add_le ρ₂.im ρ₃.im
      linarith only [h, hz₂.2.2, hz₃.2.2, hδ0, hδ1, hτe]
    simpa [zero_add] using hprinc (ρ₂.im + ρ₃.im) hτ
  have hq2' : SigmaP3L q (Real.log (q : ℝ)) 1
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₁.im + ρ₂.im - ρ₃.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ (P3 (((18 / 7 : ℝ) + lam1) / (((18 / 7 : ℝ) : ℂ)
            + (((ρ₂.im - ρ₃.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + ((18 / 7 : ℝ) + lam1) * (0 + e1) := by
    have hpt : ((ρ₁.im + ρ₂.im - ρ₃.im : ℝ) : ℂ) = ((ρ₂.im - ρ₃.im : ℝ) : ℂ) := by
      have h1 : ρ₁.im + ρ₂.im - ρ₃.im = ρ₂.im - ρ₃.im := by rw [hρ₁im]; ring
      rw [h1]
    rw [hpt]
    have hτ : |ρ₂.im - ρ₃.im| ≤ 4 := by
      have h1 := abs_le.mp hz₂.2.2
      have h2 := abs_le.mp hz₃.2.2
      rw [abs_le]; constructor <;> linarith only [hδ0, hδ1, h1, h2]
    simpa [zero_add] using hprinc (ρ₂.im - ρ₃.im) hτ
  have hq3' : SigmaP3L q (Real.log (q : ℝ)) 1
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((ρ₁.im - ρ₂.im + ρ₃.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ (P3 (((18 / 7 : ℝ) + lam1) / (((18 / 7 : ℝ) : ℂ)
            + (((ρ₃.im - ρ₂.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + ((18 / 7 : ℝ) + lam1) * (0 + e1) := by
    have hpt : ((ρ₁.im - ρ₂.im + ρ₃.im : ℝ) : ℂ) = ((ρ₃.im - ρ₂.im : ℝ) : ℂ) := by
      have h1 : ρ₁.im - ρ₂.im + ρ₃.im = ρ₃.im - ρ₂.im := by rw [hρ₁im]; ring
      rw [h1]
    rw [hpt]
    have hτ : |ρ₃.im - ρ₂.im| ≤ 4 := by
      have h1 := abs_le.mp hz₂.2.2
      have h2 := abs_le.mp hz₃.2.2
      rw [abs_le]; constructor <;> linarith only [hδ0, hδ1, h1, h2]
    simpa [zero_add] using hprinc (ρ₃.im - ρ₂.im) hτ
  have hq4' : SigmaP3L q (Real.log (q : ℝ)) 1
      (((1 + (18 / 7) / Real.log (q : ℝ) : ℝ) : ℂ) + ((-ρ₁.im + ρ₂.im + ρ₃.im : ℝ) : ℂ) * Complex.I)
      (18 / 7) lam1
      ≤ (P3 (((18 / 7 : ℝ) + lam1) / (((18 / 7 : ℝ) : ℂ)
            + (((ρ₂.im + ρ₃.im) * Real.log (q : ℝ) : ℝ) : ℂ) * Complex.I))).re
        + ((18 / 7 : ℝ) + lam1) * (0 + e1) := by
    have hpt : ((-ρ₁.im + ρ₂.im + ρ₃.im : ℝ) : ℂ) = ((ρ₂.im + ρ₃.im : ℝ) : ℂ) := by
      have h1 : -ρ₁.im + ρ₂.im + ρ₃.im = ρ₂.im + ρ₃.im := by rw [hρ₁im]; ring
      rw [h1]
    rw [hpt]
    have hτ : |ρ₂.im + ρ₃.im| ≤ 4 := by
      have h := abs_add_le ρ₂.im ρ₃.im
      linarith only [h, hz₂.2.2, hz₃.2.2, hδ0, hδ1, hτe]
    simpa [zero_add] using hprinc (ρ₂.im + ρ₃.im) hτ
  -- ### the side condition of `P₃*`
  have hside : 1 / (18 / 7 : ℝ) ^ 3
      ≤ 1 / ((18 / 7 : ℝ) + lam1) ^ 3 + 1 / ((18 / 7 : ℝ) + lam2) ^ 3
        + 1 / ((18 / 7 : ℝ) + lam3) ^ 3 := by
    have ht1 : (27 / 64) / (18 / 7 : ℝ) ^ 3 ≤ 1 / ((18 / 7 : ℝ) + lam1) ^ 3 := by
      have hpos : (0 : ℝ) < (18 / 7 : ℝ) + lam1 := by linarith only [hδ0, hδ1, hlam10]
      have h4 : (18 / 7 : ℝ) + lam1 ≤ (4 / 3) * (18 / 7 : ℝ) := by linarith only [hlam3le, hlam2le3, hlam12]
      have h1 : 1 / (((4 / 3) * (18 / 7 : ℝ)) ^ 3) ≤ 1 / ((18 / 7 : ℝ) + lam1) ^ 3 :=
        one_div_le_one_div_of_le (pow_pos hpos 3) (pow_le_pow_left₀ (le_of_lt hpos) h4 3)
      have heq : 1 / (((4 / 3) * (18 / 7 : ℝ)) ^ 3) = (27 / 64) / (18 / 7 : ℝ) ^ 3 := by
        norm_num
      linarith only [h1, heq]
    have ht2 : (27 / 64) / (18 / 7 : ℝ) ^ 3 ≤ 1 / ((18 / 7 : ℝ) + lam2) ^ 3 := by
      have hpos : (0 : ℝ) < (18 / 7 : ℝ) + lam2 := by linarith only [hδ0, hδ1, hlam20]
      have h4 : (18 / 7 : ℝ) + lam2 ≤ (4 / 3) * (18 / 7 : ℝ) := by linarith only [hlam3le, hlam2le3]
      have h1 : 1 / (((4 / 3) * (18 / 7 : ℝ)) ^ 3) ≤ 1 / ((18 / 7 : ℝ) + lam2) ^ 3 :=
        one_div_le_one_div_of_le (pow_pos hpos 3) (pow_le_pow_left₀ (le_of_lt hpos) h4 3)
      have heq : 1 / (((4 / 3) * (18 / 7 : ℝ)) ^ 3) = (27 / 64) / (18 / 7 : ℝ) ^ 3 := by
        norm_num
      linarith only [h1, heq]
    have ht3 : (27 / 64) / (18 / 7 : ℝ) ^ 3 ≤ 1 / ((18 / 7 : ℝ) + lam3) ^ 3 := by
      have hpos : (0 : ℝ) < (18 / 7 : ℝ) + lam3 := by linarith only [hδ0, hδ1, hlam3pos]
      have h4 : (18 / 7 : ℝ) + lam3 ≤ (4 / 3) * (18 / 7 : ℝ) := by linarith only [hlam3le]
      have h1 : 1 / (((4 / 3) * (18 / 7 : ℝ)) ^ 3) ≤ 1 / ((18 / 7 : ℝ) + lam3) ^ 3 :=
        one_div_le_one_div_of_le (pow_pos hpos 3) (pow_le_pow_left₀ (le_of_lt hpos) h4 3)
      have heq : 1 / (((4 / 3) * (18 / 7 : ℝ)) ^ 3) = (27 / 64) / (18 / 7 : ℝ) ^ 3 := by
        norm_num
      linarith only [h1, heq]
    have hkey : 1 / (18 / 7 : ℝ) ^ 3 ≤ (27 / 64) / (18 / 7 : ℝ) ^ 3 * 3 := by norm_num
    linarith only [ht1, ht2, ht3, hkey, hδ0, hδ1]
  -- ### the ten-term collapse
  set eS : ℝ := 24 / (δ * Real.log (q : ℝ)) + 3 * e1 + 4 * e1 with heSdef
  have hPstar := Work.P10.Pstar_collapse χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃
    (a := (18 / 7 : ℝ)) (lam1 := lam1) (lam2 := lam2) (lam3 := lam3) (δ := δ)
    (L := Real.log (q : ℝ)) (e1 := e1) (e2 := e1) (e3 := e1) (e4 := e1) (e5 := e1) (e6 := e1)
    (e7 := e1) (e8 := e1) (e9 := e1) (e10 := e1) (eS := eS)
    (by norm_num) hδ0 hLpos hlam10 hlam12 hlam23 hρ₁im hsq1 hsq2 hsq3 hprod hside
    (le_of_lt he1pos) (le_of_lt he1pos) (le_of_lt he1pos) (le_of_lt he1pos)
    (by rw [heSdef]; ring_nf; linarith only [])
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] using hp1)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] using hp2)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] using hp3)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] using hp4)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] using hp5)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] using hp6)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] using hq1)
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] using hq2')
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] using hq3')
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] using hq4')
  -- ### the weighted combination
  have hpos14 : ∀ n : ℕ, 0 ≤ Work.ZeroFreeTables.P10.comb14Raw q χ₁ χ₂ χ₃
      (Real.log (q : ℝ)) (1 + (18 / 7) / Real.log (q : ℝ)) ρ₁.im ρ₂.im ρ₃.im
      (18 / 7) lam1 n := by
    intro n
    exact Work.ZeroFreeTables.HB103.Comb14Positivity χ₁ χ₂ χ₃ (Real.log (q : ℝ))
      (1 + (18 / 7) / Real.log (q : ℝ)) ρ₁.im ρ₂.im ρ₃.im (18 / 7) lam1
      (by norm_num) hLpos hlam10 hsq1 hsq2 hsq3 hprod n
  have hcomb := case3_weighted_combination_engine (N := q) χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃
    (hpos0 := hpos14)
    (a := (18 / 7 : ℝ)) (lam1 := lam1) (lam2 := lam2) (lam3 := lam3) (δ := δ)
    (L := Real.log (q : ℝ)) (e1 := e1) (e2 := e1) (e3 := e1) (eP := e1) (eS := eS)
    (eps := 6 * e1 + 5 * e1 + 48 / (δ * Real.log (q : ℝ)))
    (by norm_num) hδ0 hδ1 hLpos hlam10 hlam12 hlam13 (le_of_lt he1pos) (by rw [heSdef]; positivity)
    (by rw [heSdef]; ring_nf; linarith only [])
    hsq1 hsq2 hsq3 hprod hb1 hb2 hb3 hpole
    (by simpa only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_neg] using hPstar)
  -- ### HB (10.14)
  refine p1014_of_bridge_eps (δ := lam1 / (6 / 7))
    (X₁ := ((18 / 7 : ℝ) + lam1) / (18 / 7))
    (X₂ := ((18 / 7 : ℝ) + lam1) / ((18 / 7 : ℝ) + lam2))
    (X₃ := ((18 / 7 : ℝ) + lam1) / ((18 / 7 : ℝ) + lam3))
    (eps := 6 * e1 + 5 * e1 + 48 / (δ * Real.log (q : ℝ))) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · positivity
  · field_simp
    ring
  · have hpos : (0 : ℝ) < (18 / 7 : ℝ) + lam2 := by linarith only [hδ0, hδ1, hlam20]
    rw [le_div_iff₀ hpos, div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have hδ : lam1 / (6 / 7) = 7 * lam1 / 6 := by ring
    rw [hδ]
    nlinarith only [hlam10, hlam20, hlam267, hlam3le, hlam2le3, hδ0, hδ1]
  · have hpos : (0 : ℝ) < (18 / 7 : ℝ) + lam3 := by linarith only [hδ0, hδ1, hlam3pos]
    rw [le_div_iff₀ hpos, div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    have hδ : lam1 / (6 / 7) = 7 * lam1 / 6 := by ring
    rw [hδ]
    nlinarith only [hlam10, hlam30, hlam367, hlam3le, hδ0, hδ1]
  · exact le_of_lt hε
  · rw [he1def]
    linarith only [hbud, hε]
  · have h6 : (6 / 7 : ℝ) * (lam1 / (6 / 7)) = lam1 := by ring_nf
    rw [h6]
    exact hcomb

end Work.ZeroFreeTables
