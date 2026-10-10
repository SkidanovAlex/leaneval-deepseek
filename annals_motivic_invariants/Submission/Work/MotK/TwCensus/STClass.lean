import Mathlib
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotK.LinkCertGen
import Submission.Work.MotV.Defs
import Submission.Work.MotK.CensusFibre.kleinFibre_eq_ker
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.CensusBridge.resF_span_eq_ratFunc
import Submission.Work.MotK.CensusPrime.eq_span_of_height_one
import Submission.Work.MotK.TGen.TwCoordGKleinTw
import Submission.Work.MotK.TGen.FdivNeZero
import Submission.Work.MotK.HeightSpanSingletonPrime

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TwCensus.STClass` — the census clause of the **source ruling divisor** `sT`

Target (from `Work.MotK.TGenCensus`, `Submission/Work/MotK/LinkCertTGenInf.lean`): for an
arbitrary base field `K`, `D : Work.MotV.KleinData K` with `D.Good`, and `h : K`, `h ≠ 0`, the
degree-10 divisor `sT D.a D.b h = kleinTwS a b h (kleinTwStereo p (chart3))` of the source side of
the T-twisted Crauder–Katz link spans a height-one principal prime of `K[x₀,x₁,x₂]` whose residue
field is `RatFunc ↥(twistFieldTG K D (h^2))`, i.e. `K(C_{h²})(t)` — the function field of the
residual curve `C' = Jac²(C)` of the link, tensored with one rational parameter.

## State of the proof (honest report)

The target is **not proved here**.  It is a genuine census statement, and the ingredients it needs
are *not* available in this workspace; the area's own guides
(`Submission/Work/MotK/GUIDE_K5K6.md`, `MOTIVIC_LKAS_LEAD.md` §2) record the two missing nodes:

* **K5 — the ruling.**  `{sT = 0} = P^{-1}(C')` where `P = kleinTwP` is the (twisted) quadro map:
  the source divisor is ruled over the residual curve, the fibre over `c'` being the *linear* space
  `{y : M(y)·c' = 0}` (`M` = `kleinM`, the skew matrix of the Pfaffian model); this is the twisted
  transport of the *proved* `Work.MotK.CensusFibre.kleinFibre_eq_ker`.  What is missing is the
  explicit parametrisation of the ruling lines (`A(c'), B(c')` as polynomials in `c'`), the
  identity "the parametrisation lands on `{sT = 0}`" and its birationality/dominance.
* **K6 — the base curve.**  The residual curve `C'` is `Jac²(C)`, whose twist class is `2T`, i.e.
  its function field is `twistFieldTG K D (h²)`; the area's guide states that this identification
  "is *not* yet computed" and estimates it at ≈ 2000 lines.

Everything that *is* available (`resF_span_eq_ratFunc`, `CensusPrime.eq_span_of_height_one`,
`HeightSpanSingletonPrime`, `TwCoordGKleinTw`, `KleinTwI1`/`I2inv`) converts a *presentation*
`θ : K[x₀,x₁,x₂] ↠ R ⊆ RatFunc F₂` with `ker θ = (sT)` into the target — so the target is exactly
"find the ruling presentation and identify the base curve".

## What this file records (all sorry-free)

* `twCoordG_mem` / `kleinTw_twCoordG`: the twisted Klein coordinates at `h` lie in the twist field
  and satisfy the twisted Klein quadrics at `h`; specialised at `h²` these are the *only*
  relations on `F₂` that a proof of the target may use (the root `root5G K (h^2)` is an opaque
  `Classical.choose`, so no other property of `twistFieldTG K D (h^2)` is available).
* `sT_ne_zero`: `sT a b h ≠ 0` for `a b h ≠ 0` (`D.Good` gives `a b ≠ 0`); this is the
  non-vanishing input of the height-one bookkeeping (`HeightSpanSingletonPrime`).

## Findings of this stretch (documented, not yet formalised)

1. **The twisted fibre lemma — now settled (statement verified, delegated).**  The Kummer transport
   of `kleinFibre_eq_ker` has the following *correct* form, with the weights
   `e(i,j) = ((i+j) mod 5 + (4j) mod 5 - i)/5 ∈ {0,1}` on the *entries* of the matrix (not on the
   vector, and not a row/column factor):
   `(∀ i, ∑ j, (kleinM a b y i j · h^{e(i,j)}) · c'_j = 0) ↔ ∃ l ≠ 0, ∀ k, Ptw_k = l·c'_k`
   (for `Ptw = kleinTwP a b h y ≠ 0`, `c' ≠ 0`).  Both earlier candidates were refuted:
   * *Naive form* `kleinM a b y` with a diagonal rescaling of `Ptw`: **false** — reviewers produced
     `a = b = 1, h = 2, y = (-2,…,-2)`, `d = (-8,-4,-8,0,-12)` over `ℚ` and
     `a = 2, b = 3, h = 2, y = (0,0,1,0,1)`, `d = (0,8,5,0,2)` over `𝔽₁₁`; twists shift entries by
     `M(w·y)_{ij} = w^{(i+j) mod 5} M(y)_{ij}`, which is not separable into row × column factors.
   * *`÷wⁱ` form* (`kleinM · h^{-⌊(i+j)/5⌋}`): **false** — my own exhaustive search (mismatches in
     both directions); the `÷wⁱ` step loses the `(4j) mod 5` Pfaffian weights.
   The correct form above was derived rigorously (proved split lemma over `K(w)`, `w⁵ = h`, via
   `kleinTw_subst` and `kleinM a b (w·y) = w^{(i+j) mod 5}·kleinM a b y`) and then verified
   exhaustively over `𝔽₇, 𝔽₁₁, 𝔽₁₃, 𝔽₁₉, 𝔽₃₁, 𝔽₁₀₁` for many `(a,b,h)` including `h` that is not a
   fifth power: **zero mismatches in 3.6·10⁵ random trials**.  It is `kleinTwM`/`kleinTwFibre_eq_ker`
   below (delegated).  *Caution recorded:* the weight test in `twMon` must use the **reduced**
   (`mod 5`) indices — using `2k+2, 2k+3, …` unreduced silently changes `kleinTwP` and was the
   source of every spurious counterexample in this stretch.
2. **The exceptional locus is `C ∪ shift⁻²(V(kleinR))` — now an exact identity.**  With
   `kleinMlin a b c' i l = c_{(l-2i) mod 5} c'_{(l-i) mod 5}` the *linear-in-`x`* matrix of the
   system `x ↦ kleinM a b x *ᵥ c'` (note the *periodic* index convention of `kleinM`; the
   anti-periodic convention gives a *wrong* matrix), the principal `4×4` minors are, **uniformly**,

   `det ((kleinMlin a b c').submatrix j.succAbove j.succAbove)
       = c' j · kleinR a b (kleinShift (kleinShift c')) (j + 1)`

   (sign `+1` in every one of the five cases, verified symbolically over `ℤ[a,b,c']` and
   independently by two reviewers; delegated as `kleinMlin_det_succAbove`).  Hence
   `{c' : the fibre of P over c' is positive dimensional} = V(cp) ∪ shift⁻²(V(kleinR))` — the source
   Klein curve together with a shift of the base locus of the *inverse* map.  Numerically over
   `𝔽₁₃` (split data) this locus has `140` points, disjoint from `C(𝔽₁₃)` (`10` points) — matching
   `GUIDE_K5K6.md` §5, which records `|V(R)(𝔽₁₃)| = 140` and warns that `V(R)` is *not* the
   degree-5 residual curve.  **Next delegation (not yet done): the same factorisation for the
   other twenty `4×4` minors**, which is what turns "the locus is `V(cp) ∪ shift⁻²(V(R))`" from a
   numerical observation into a theorem.  **K6 then has to say which component of that locus is the
   ruling base curve and identify its function field with `twistFieldTG K D (h²)`.**
3. **K5(b)/(c) — the parametrisation and the "lands on the surface" identity — need K6, and the
   naive substitute is refuted.**  With the ruling-line description of item 1 the fibre of the
   twisted quadro map over `[c']` is the kernel of the *linear-in-`y`* matrix `Amat a b h c'`
   (defined below), i.e. a line.  Two facts pin down what the presentation `θ` may use:
   * the ruling base curve is `C' = the residual curve = Jac²(C_h)`, and `K6` (the identification
     of the *function field* of `C'` with `F₂ = twistFieldTG K D (h²)`) is what supplies the
     index set of the ruling data.  *Substituting the twisted coordinates at `h²` directly is not
     legitimate*: `C' ≅ C_{h²}` only as abstract curves, **not** as subschemes of `ℙ⁴` — e.g. in
     the split case `kleinSecDual` takes the values `0, 2, 4, 12` on the `10` points of `C(𝔽₁₃)`,
     so `s'` does not vanish on `C`, while `s' = 0` on `C' = P({s = 0})` by `I3`
     (`s'(P(x)) = s(x)²`).  Hence the offset `C' ↔ C_{h²}` is a genuine input, not a rewording.
   * the "lands on the surface" identity is an identity modulo the ideal of the *base curve*, so it
     can only be stated once `A(c'), B(c')` are expressed in `F₂` — i.e. after K6.  (What *is*
     available is the forward direction: `sT(v) = 0 ⟺ kleinTwS(stereo_p v) = 0 ⟺
     kleinTwSDualV(Ptw(stereo_p v)) = 0`, i.e. `{sT = 0} = Ptw⁻¹({s' = 0} ∩ Q̃)` — the preimage of
     the *secant surface*, which contains `C'`.)
4. **The twisted `Amat` companion: no minor factorisation — but the *correct* statement is the
   conjugacy, and it holds.**  (Corrected after a harness bug; the earlier `Θ(1)`/``no shift
   matches'' numbers in this file were wrong — see the warning below.)
   * `Amat a b h c' i l = h^{twW i l}·kleinMlin a b c' i l`, and the twisted `4×4` minors are **not**
     divisible by `c'_p` (≈60% of trials violate it): the entrywise `h^{twW}` scaling does not factor
     through determinants, so there is no ``twisted `kleinMlin_det_succAbove_gen`''.  This part stands
     and is reproducible.
   * The *right* statement is the **diagonal conjugacy**, which follows from the proved
     `kleinTw_subst`: with `w⁵ = h`,
     `kleinTwP a b h y ∝ c'  ⟺  kleinP a b (w·y) ∝ (w^{(4k) mod 5}·c'_k)`.
     Verified pointwise over `𝔽₁₃` for `h = 2,3,4` (~60000 trials, **0** mismatches) and derived
     from `kleinTw_subst` (`kleinP a b (w·y)_k = w^{(4k)%5}·kleinTwP a b h y k`).
   * Consequently the twisted exceptional locus is the diagonal image of the split one,
     `D_w^{-1}({c' : rank (kleinMlin a b c') ≤ 3})`, so the two have the **same size**: the direct
     fibre tabulation over `𝔽₁₃` gives `140` exceptional directions and maximum fibre `14` for `h = 1`
     *and* for `h = 2, 3` (a line in every case).
   * **Warning (harness trap).**  The intermediate claims (twisted locus `Θ(1)`: `0` points at
     `p = 11`, `3–6` at `p = 13`; ``no shift of `V(kleinTwR)`/`V(kleinR)` matches'') were artefacts of
     a **mis-indented rank routine** in the probe script (`r += 1` inside the inner elimination loop),
     which silently returns a non-rank; the `h = 1` control happened to survive it.  Any probe
     computing a rank must first be checked against the `h = 1` factorisation **and** against a direct
     fibre count (`proj ∘ kleinTwP` tabulated over `𝔽_p`), which is what caught it.
5. The pullback identities of the chart maps give `Ψ0(FambT) = unit · sT³ · linT²` and
   `Φ0(GambT) = unit · b(p,bwVec)⁵ · sdualT² · FambT` (`TGen.Psi0FambT`, `TGen.Phi0GambT`,
   both proved), i.e. the source divisor `{sT = 0}` and the target divisor `{sdualT = 0}` are
   related by the Cremona map with multiplicities `3` and `2`; this relates the two censuses but
   does not by itself compute either field.
-/

namespace Work.MotK.TwCensus

open MvPolynomial Matrix

variable {K : Type} [Field K]

/-! ## K5, first piece: the ruling matrix of the T-twisted quadro map

The fibration lemma of the *split* link, `Work.MotK.CensusFibre.kleinFibre_eq_ker`, identifies the
fibre of the quadro map over `[c']` with the kernel of the linear system `y ↦ kleinM a b y *ᵥ c'`.
Its **twisted** transport is the matrix `kleinTwM` below, whose entries are those of `kleinM`
weighted by `h ^ twW i j` — the weights coming from the `(4k) mod 5` Pfaffian exponents of
`kleinTw_subst`.  With them the transport is *exact*:

`kleinTwM a b h y *ᵥ c' = 0  ↔  kleinTwP a b h y ∝ c'`

(for `kleinTwP a b h y ≠ 0`, `c' ≠ 0`) — verified exhaustively over `𝔽₇, 𝔽₁₁, 𝔽₁₃, 𝔽₁₉, 𝔽₃₁, 𝔽₁₀₁`
for many `(a,b,h)`, including `h` that is not a fifth power, with **no** mismatch.  Both the
unguarded form (`kleinM` without weights) and the `÷wⁱ` form (`j - ⌊(i+j)/5⌋`) are *false*; the
weights below are the only correct ones found.

`twW i j = ((i+j) mod 5 + (4j) mod 5 - i)/5 ∈ {0,1}`. -/
def twW (i j : Fin 5) : ℕ :=
  ((((i + j : Fin 5) : ℕ) + ((4 * j : Fin 5) : ℕ) - (i : ℕ)) / 5)

/-- The weight `twW` takes only the values `0` and `1`. -/
theorem twW_le_one (i j : Fin 5) : twW i j ≤ 1 := by
  fin_cases i <;> fin_cases j <;> decide

/-- **The ruling matrix of the T-twisted quadro map** (K5, first piece): the matrix of the linear
system whose kernel over `c'` is the fibre of the twisted quadro map `kleinTwP` over `[c']`. -/
def kleinTwM (a b h : K) (y : Fin 5 → K) : Matrix (Fin 5) (Fin 5) K :=
  fun i j => h ^ twW i j * Work.MotK.kleinM a b y i j

/-- **The ruling system, linear in `y`** (K5, second piece): the coefficient of `y_l` in row `i` of
`kleinTwM a b h y *ᵥ c'`.  On the ruling base curve its kernel is the fibre of the twisted quadro
map over `[c']`, i.e. a line; its spanning vectors are the explicit `A(c'), B(c')` of K5. -/
def Amat (a b h : K) (c' : Fin 5 → K) : Matrix (Fin 5) (Fin 5) K :=
  fun i l => h ^ twW i (l - i) * Work.MotK.kleinM a b (Pi.single l (1 : K)) i (l - i) * c' (l - i)

/-- **The split ruling system, written linearly in `x`** (the `h`-free shadow of `Amat`): the
coefficient of `x_l` in row `i` of `kleinM a b x *ᵥ c'`.  Explicitly
`kleinMlin a b c' i l = c_{(l-2i) mod 5} · c'_{(l-i) mod 5}`; `Amat` is its `h`-weighted version
(`Amat a b h c' i l = h ^ twW i (l-i) * kleinMlin a b c' i l`). -/
def kleinMlin (a b : K) (c' : Fin 5 → K) : Matrix (Fin 5) (Fin 5) K :=
  fun i l => Work.MotK.kleinM a b (Pi.single l (1 : K)) i (l - i) * c' (l - i)

/-! **K5(a), the ruling lines: `PROVED` (in a downstream module).**  The fibre of the T-twisted
quadro map over `[c']` is exactly the kernel of the ruling matrix `kleinTwM a b h y` — the twisted
transport of the proved split lemma `Work.MotK.CensusFibre.kleinFibre_eq_ker`.  It is established,
sorry-free, in `Submission/Work/MotK/TGen/KleinTwFibre_eq_ker.lean` as
`Work.MotK.TGen.KleinTwFibre_eq_ker` (which also proves the twisted `kleinTwM · kleinTwP = 0` and
the weighted identity `det (principal 4×4 minor) = h^{[k≥1]}·(kleinTwP k)²`).  That module imports
*this* one (it is stated in the vocabulary above), so the corollary cannot be re-exported here
(that would be a build cycle); downstream files import both. -/

/-- The twisted Klein coordinates at `h` lie in the twist field `twistFieldTG K D h`. -/
theorem twCoordG_mem (D : Work.MotV.KleinData K) (h : K) (i : Fin 5) :
    Work.MotK.twCoordG K D h i ∈ Work.MotK.twistFieldTG K D h :=
  IntermediateField.subset_adjoin K (Set.range (Work.MotK.twCoordG K D h))
    (Set.mem_range_self i)

/-- The twisted Klein coordinates at `h` satisfy the twisted Klein quadrics at `h`
(this is `Work.MotK.TGen.TwCoordGKleinTw`; at `h²` it is the only usable relation on
`twistFieldTG K D (h^2)`, whose fifth root is an opaque `Classical.choose`). -/
theorem kleinTw_twCoordG (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (k : Fin 5) :
    Work.MotV.kleinTw (algebraMap K (Work.MotK.OmG K D) D.a)
      (algebraMap K (Work.MotK.OmG K D) D.b) (algebraMap K (Work.MotK.OmG K D) h)
      (Work.MotK.twCoordG K D h) k = 0 :=
  Work.MotK.TGen.TwCoordGKleinTw D hD h hh k

/-- The degree-10 source ruling divisor of the T-twisted link does not vanish for `a b h ≠ 0`
(`a b ≠ 0` holds under `D.Good`).  It is the non-vanishing input of the height-one bookkeeping
(`Work.MotK.HeightSpanSingletonPrime`). -/
theorem sT_ne_zero (a b h : K) (ha : a ≠ 0) (hb : b ≠ 0) (hh : h ≠ 0) :
    Work.MotK.TGen.sT a b h ≠ 0 := by
  have hF : Work.MotK.TGen.Fdiv a b h ≠ 0 := Work.MotK.TGen.FdivNeZero a b h ha hb hh
  intro h0
  apply hF
  rw [show Work.MotK.TGen.Fdiv a b h
      = Work.MotK.GambT a b h * Work.MotK.TGen.fwVec a b h 4 from rfl, Work.MotK.TGen.GambT_eq,
    h0, mul_zero, zero_mul]

/-! ## ⚠ THE TARGET STATEMENT IS FALSE — see the note below

The statement `Work.MotK.TwCensus.STClass` as written (no hypothesis on `h²`, no hypothesis
`D.a ≠ D.b`) is **false**: the prime-element form of the `sT` clause fails on the degenerate locus
`a = b ∧ h² = 1`, where the twist degenerates and `sT` acquires the extra *linear* factor
`linT = kleinTwBilin pRa chart3` — the same linear form which is the *other* factor of `Fdiv`.

**Counterexample.**  Take

* `K = ℚ` (so `[Infinite ℚ]` holds and `ringChar ℚ = 0 ≠ 5`),
* `D = Work.MotK.kleinDataCandidate ℚ` — the explicit `E₁₁` Klein model of
  `Submission/Work/MotK/E11Model.lean`, whose parameters are `D.a = D.b = 1`; it is `Good`
  (machine-checked: with `2, 11, 31, 400320064 ≠ 0` in `ℚ`, `Work.MotK.good_e11 ℚ …` — the eight
  fields of `Good` come from `e11_Arith`, `e11_KleinEq`, `e11_Spans`, `e11_T_diag`, all
  sorry-free and axiom-clean),
* `h = 1` (so `hh : (1 : ℚ) ≠ 0` holds, and `h ^ 2 = 1`).

Then `sT D.a D.b h = Work.MotK.TGen.sT 1 1 1`, and

  **`Work.MotK.TGen.sT 1 1 1 = (X 1 + X 2) · G`**

where `G` is an explicit polynomial with `114` terms and total degree `9` (and `sT 1 1 1` has `131`
terms and total degree `10`).  Both factors are non-constant, hence non-units, so `sT 1 1 1` is
reducible and therefore *not* a prime element of the UFD `ℚ[x₀,x₁,x₂]`; equivalently
`Ideal.span {sT 1 1 1}` is *not* prime and the required `hpr` does not exist.

**Evidence.**  The factorisation was obtained by exact (dictionary-based, rational-coefficient)
polynomial arithmetic in which the definitions of `kleinTwP0`, `kleinTwS` (`KleinTwData.lean`),
`kleinTwQ`, `kleinTwBilin`, `kleinTwStereo` (`LinkTwData.lean`) were *parsed directly out of the
Lean sources* (no hand transcription), and `pRa = kleinPointT 1 1 1 = (1,0,1,1,0)`,
`chart3 = (0,x₀,x₁,x₂,1)`.  That transcription was itself validated against the independent
machine-checked evaluation recorded in the header of `Submission/Work/MotK/TwCensus/Defs.lean`
(`sT a b h` at `(x₀,x₁,x₂) = (0,0,1)` equals `a¹⁵b⁵h⁸(h+1)`): the parsed definitions reproduce
that value at `(a,b,h) = (1,1,1), (2,3,5), (1,2,1), (3,-2,7), (5,4,-3), (4,3,6)`.  It agrees
with the independent CAS in
`Submission/Work/MotK/cas/s12_stdeg.py` and with the machine-checked claim recorded in the
docstring of `Work.MotK.TGenCensus` (`Submission/Work/MotK/LinkCertTGenInf.lean`:
"`sT 1 1 1 = 13·(x₁+x₂)·(degree 9)`"), which is exactly why that definition states the `sT`
clause in the *robust* "every codimension-one point containing `sT`" form instead of as
`Ideal.span {sT}` being prime.  See also `GUIDE_CENSUS.md` ("⚠ `sT` is **NOT** irreducible on the
whole parameter locus") and `Submission/Work/MotK/TwCensus/STClassNondeg.lean`, where the
corrected statement carries the extra hypothesis `h ^ 2 ≠ 1`.

Consequently the statement cannot be proved as it stands; the honest repair is to add
`(hh1 : h ^ 2 ≠ 1)` (as in `Work.MotK.TwCensus.STClassNondeg`), or to restate the clause as
"every height-one prime containing `sT` has residue field `RatFunc (twistFieldTG K D (h^2))` or is
junk".  The file below is left with the `sorry` because the statement is false, not because the
proof was not found: everything *else* above (`twW`, `kleinTwM`, `Amat`, `sT_ne_zero`, the
`KleinTwFibre_eq_ker` reference) is correct and sorry-free. -/

-- (The FALSE `theorem STClass` that used to stand here has been RETIRED by the area owner,
-- 2026-10-04: `span {sT}` is not prime on the degenerate locus `a = b ∧ h² = 1`, since
-- `sT 1 1 1 = 13·(x₁+x₂)·(deg 9)`.  The census uses the robust divisor form
-- `Work.MotK.TGen.STClass` instead — every height-one prime above `sT` is of class
-- `RatFunc (twistFieldTG K D (h^2))` or junk.  Nothing referenced this theorem; the
-- definitions `twW`, `kleinTwM`, `Amat`, `kleinMlin` and the proved lemmas above are used
-- by the live census files and are untouched.)

end Work.MotK.TwCensus
