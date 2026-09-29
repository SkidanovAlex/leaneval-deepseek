import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.H_conv
import Submission.Work.A14D.logCoeff_exists
import Submission.Work.A14D.LC_setup
import Submission.Work.A14D.log_structured_vanishes
import Submission.Work.A14D.Dzc_helpers
import Submission.Work.C17g.segment_primitive
import Submission.Work.A14D.LC_A_defs
import Submission.Work.A14D.jumpI_defs
import Submission.Work.A14D.jPrim_hasDerivAt
import Submission.Work.A14D.BU_analytic_agree
import Submission.Work.A14D.SU_relation_two
import Submission.Work.A14D.jump_G_ident
import Submission.Work.A14D.jump_I_ident
import Submission.Work.A14D.pure_part_lower
import Submission.Work.A14D.half_log_vanishes
import Submission.Work.A14D.decomp_G
import Submission.Work.A14D.decomp_I
import Submission.Work.A14D.decomp_G_L
import Submission.Work.A14D.decomp_I_L
import Submission.Work.A14D.Dw_extends
import Submission.Work.A14D.Dw_extends_L
import Submission.Work.A14D.om1_geometry
import Submission.Work.A14D.ppc_aux
import Submission.Work.A14D.wC_im_neg
import Submission.Work.A14D.primSeg_hasDerivAt
import Submission.Work.A14D.DyIter_diffOn_of_isOpen
import Submission.Work.A14D.preconnected_SU_diff_two

/-!
# `Work.A14D.relation_to_LC_A` — status and route

**What the lemma says.**  From the `ℚ[y]`-relation `Σᵢ Pᵢ·fourteenᵢ = 0` for the fourteen
functions of Theorem A, together with the analytic data (`HU, HL` the continuations of
`H = aH_A+bH_B+cH_C` to the half planes `SU, SL`, `D = HU − HL` the jump, `y9` the holomorphic
solution of `LZ = 0` at `1/9`, `κU, κL` the log coefficients of `D` at `1/9`), conclude the
`(LC)` identity: with `J_i` the antiderivatives of `y^{−i}y' y9` vanishing at `1/9`,
```
κ * ( Σ_{k<4} p_k(y(z)) ∂_y^k y9(z) + Σ_{j<3} q_j(y(z)) J_j(z) ) = 0    (z in ball (1/9) δ)
```
for `κ = κU` and `κ = κL`, where `p_k = P_{5+k}`, `q_j = P_{11+j}`.

**Route established here (design §4).**
1. `κU = κL` (hypotheses: the same principal `log(z−1/9)` on both half disks; if `κL ≠ κU`
   the function `(κL−κU) y9 log + (h_L−h_U)` would be holomorphic on `halfL δ`, impossible).
2. Pull the relation back along `y = y(z)`: `Σᵢ Pᵢ(y(z)) Fᵢ(z) = 0` on a disc, where `Fᵢ` is the
   pulled-back entry (`F₅ = H + H∘w`, its `∂_y`-derivatives, the three primitives, and the seven
   pure pullbacks `Bᵢ∘y`, whose closed forms in `x` are `Work.C7.g_form`: `g₁ = 2y − w·log(1−x)`,
   `g₂ = −log(1−x)²/2`, `g₃ = (x−φ)(2Li₂ + ½log(1−x)²)`, `g₄ = (x/(x−1))·Jps`).
3. Take the jump `J(F) = F|SU − F|SL`, an object on `Om1`; it is `ℂ(x)`-linear and commutes with
   `d/dx`, `∂_y` and primitives.  Because `(Sym⁺H)∘y = H + H∘w`, the `G`-jump is
   `J(𝒢) = D − D∘w = jumpH D`, and the `∂_y`-iterates are `jumpG D k`.  Hence
   `Σᵢ Pᵢ(y(z))·JFᵢ(z) = 0` on `Om1`.
4. Each `JFᵢ` equals `Aᵢ(z)·log(z−1/9) + Bᵢ(z)` on both half disks with `Aᵢ = jumpCoeff κ y9 i`
   (`κ·∂_y^k y9`, `κ·J_j`, `0`) and `Bᵢ` *single-valued* (differentiable on the punctured ball;
   the pure entries are analytic even at `1/9`, and for them `Aᵢ = 0`).
   This is `LC_jump_package`.
5. **Extraction of the coefficient (the assembly, to be written here).**  With
   `G := Σᵢ Pᵢ(y(·))·Aᵢ` (analytic on the ball) and `B := Σᵢ Pᵢ(y(·))·Bᵢ` (differentiable on the
   punctured ball), the relation reads `G(z)·log(z−1/9) + B(z) = 0` for `z` in *both* `halfU δ`
   and `halfL δ`.  Taking the limits at a real point `z₀ ∈ (1/9−δ, 1/9)` from above and from
   below gives `G(z₀)(log t + iπ) + B(z₀) = 0` and `G(z₀)(log t − iπ) + B(z₀) = 0`, hence
   `2πi·G(z₀) = 0`, so `G` vanishes on the real interval `(1/9−δ, 1/9)`, hence identically on the
   ball.  Since `G = κ·X`, this is the conclusion (for `κ = κU = κL`).
6. The three functions `J : Fin 3 → ℂ → ℂ` of the conclusion are the primitives
   `jPrim y9 i` (differentiable on `ball (1/9) δ`, vanishing at `1/9`, with the required
   derivative), whose existence is Mathlib's `DifferentiableOn.isExactOn_ball` on the convex ball.

**Status (this module).**  Proved here: `exists_J_aux` (the existential half of the conclusion),
`gIdx`/`iIdx`/`jumpCoeff_gIdx`/`jumpCoeff_iIdx` (the index bookkeeping: `jumpCoeff` on the four
`G`-slots is `κ·∂_y^k y9`, on the three integral slots `κ·jPrim y9 i`), `sum_jumpCoeff_eq` (the
`log`-coefficient block of the relation equals `κ·X`), `prim_unique` (two primitives of
`y^{-i} y' y9` agreeing at `1/9` are equal — this pins the `J i` of the conclusion),
`logcoeff_zero_of_halfs` (= `log_structured_vanishes`), `Xfun` (the `(LC)` expression) and
(delegated, proved) `kappa_both_zero_of_halfs`: the *extraction*, i.e. if a single function `B`
holomorphic on the punctured ball satisfies `κ^σ X log(z−1/9) + B = 0` on the two half discs,
then `κU·X = κL·X = 0` on the ball.

**State of the transfer (session 3, accurate account; supersedes the sketches below).**

*Proved and importable*: `Work.A14D.exists_J_aux` (the existential half of the conclusion),
`jPrim_ninth` (here), `prim_unique`, `gIdx`/`iIdx` and the identifications
`jumpCoeff_gIdx`/`jumpCoeff_iIdx`/`sum_jumpCoeff_eq` (the target's `(LC)` expression is exactly
`κ * Σ_i pAtY (P i) z * jumpCoeff κ y9 i z`), and — delegated — `Work.A14D.kappa_both_zero_of_halfs`
(the extraction: two log-structured relations on the two half-discs with a *common* remainder and
analytic coefficient `X` force `κU * X = κL * X = 0`) plus `Work.A14D.relation_to_LC_A_of_halfs`
(the same in the shape needed here).  New in this session (`import` them):
`Work.A14D.fourteen_coeff_bounds` (coefficient bounds for the fourteen entries, rate `R > 1/5`),
`Work.A14D.pullback_rel_disc_A` (the pullback relation `Σᵢ pᵢ(y(z))·(Σ' k [yᵏ]fᵢ·(yC z)^k) = 0` on
`‖z‖ ≤ 34/100`), `Work.A14D.GZ_eval` (`Σ_k [yᵏ](GZ a b c)·(yC z)^k = Hfun z + Hfun (wC z)` on
`‖z‖ ≤ 39/100`), `Work.A14D.pure_pullback_cont` (the seven pure pullbacks continue to `SU \ {2}`
and `SL \ {2}`), `Work.A14D.jPrim_hasDerivAt` (the canonical primitives carry the derivative of
the conclusion; with `jPrim_ninth` and `prim_unique` this pins the existential `J` to `jPrim`).

*The remaining route, step by step.*  (1) On the disc `‖z‖ ≤ 34/100` the pullback relation holds
(`pullback_rel_disc_A`); each entry's pullback there is `Σ' k [yᵏ]fᵢ·(yC z)^k`, which by
`GZ_eval`/`DyIter_comp_yC` (generic) is `Hfun z + Hfun (w z)` and its `∂_y`-iterates for the `G`
slots, and the primitives of those for the three integral slots.  (2) The *`SU`-branch* of each
entry is an analytic function on `SU` equal to the pullback germ on `SU ∩ ball 0 1`: for the `G`
slots it is `HU + HL∘w` (using `w(SU) = SL`), for its `∂_y`-iterates the same with `∂_y`, for the
integral slots the primitives, and for the pure slots the continuations from
`pure_pullback_cont`.  Gluing these with the pullback functions on `{im > 0}` and applying the
identity theorem on the connected domain `SU ∪ {im > 0}` (all these functions analytic there) gives
the relation `Σᵢ pᵢ(y(z))·Fᵢ^{SU}(z) = 0` on `SU`.  (3) **The `SL`-relation is then free**: every
entry is a function of `y`, and `y ∘ w = y` (`Submission.CDT.symp_y_invariant`), so the `SL`-branch
is the `w`-transport of the `SU`-branch, `Fᵢ^{SL}(z) = Fᵢ^{SU}(w z)`; since `pᵢ(y(w z)) = pᵢ(y(z))`
the relation on `SL` is the `SU`-relation at `w z`.  (4) Subtracting the two relations gives the
*jump relation* `Σᵢ pᵢ(y(z))·(Fᵢ^{SU}(z) − Fᵢ^{SL}(z)) = 0` on the wedge `SU ∩ SL`; the jumps are
`∂_y^k(D − D∘w)` for the four `G`-slots (`D = HU − HL` on the wedge by `hDj`) and the primitives of
`y'·y^{−i}·(D − D∘w)` for the three integral slots, while the pure ones vanish identically *near
`1/9`* (their `SU`- and `SL`-branches both restrict to the analytic pullback on `ball 0 1`, which
contains the base points and `1/9`).  Each jump function is analytic on the connected
`Om1 \ {2}` (`D` is analytic on `Om1`, `w(Om1) ⊆ Om1`, `D_y` has poles only at `2`), so the
identity propagates from the wedge to `ẞ \ {ninth}`.  (5) **Log extraction**: the log coefficient
at `1/9` of the jump relation is `κ^σ·X` (`sum_jumpCoeff_eq`), and it must vanish; the remainders
are allowed to have poles at `1/9` because the extraction lemma `log_structured_vanishes`
(`= logcoeff_zero_of_halfs` here) only demands analyticity on the *punctured* disc.  Hence
`κU·X = κL·X = 0` on `ball (1/9) δ`, which is the conclusion.

*Traps (do not re-derive).*  (a) The naive argument "`H`'s continuation to `Om1` is single-valued,
hence `HU = HL` on the wedge" is **wrong**: `Om1` is simply connected but any path in it from a
point of `SU ∩ ball 0 1` to a point of `SL ∩ ball 0 1` goes around the point `1`, where `H` has a
genuine `log²` singularity, so the two branches differ by that monodromy — this is exactly the
`D ≠ 0` of `Work.A14D.D_ne_zero`/`jump_not_zero_Om1`.  (b) The jump of the `G`-entry is therefore
`D − D∘w`, not `0`.  (c) `κU` and `κL` need not be equal; the extraction must handle both.
(d) The `y`-series of `Sym⁺(H)` converges with radius `≥ 1/4` **under `ARel`** (because `H` itself
overconverges to radius `1`); the numerically divergent series is that of `Sym⁺H_A` alone, which is
irrelevant here.  (e) `Work.C17.Bsubst_poly_growth` says the coefficients of the pure pullbacks
have *polynomial* growth, i.e. radius `≥ 1`, not that they are entire
(cf. `pullback_B2_hasSum`, which exhibits a singularity at `z = 1`).


**SESSION 6 FINDINGS (this supersedes the session-5 note below).**

The session-5 conclusion "both natural routes are blocked" was based on requiring the remainder
`B` of the `log`-structured identity to be holomorphic on the whole *punctured disc*; that
requirement is too strong.  What is actually needed (and true here) is:

* the identity `A z · log (z − 1/9) + B z = 0` only on the *upper* half disc `halfU δ`,
* with `A` holomorphic on `ball ninth δ` and `B` a sum of a meromorphic-at-`1/9` function and of
  functions whose germ at `1/9` extends holomorphically across the real axis (the `D ∘ w` term and
  the pure terms are of this second kind: `D` restricted to a neighbourhood of `-1/8` in the lower
  half plane extends across the slit because `-1/8` is a *regular* point of `LZ`, and the pure
  pullbacks are holomorphic on the unit disc, hence on `ball ninth δ`).

That weaker form is exactly `Work.A14D.extract_log_half` (proved in this file and in the module
`Submission.Work.A14D.extract_log_half`): clearing the pole by multiplying with `(z − 1/9)^m`
turns the one-sided identity into a two-sided one with both sides holomorphic on the *whole* disc
(`Dzc_log_structured_extend`), and `log_structured_vanishes` finishes.

With that, the design's steps (J) + (Λ) do close.  Concretely, the plan now being implemented is:

1. `BU : Fin 14 → ℂ → ℂ`, the `SU`-branch of the fourteen pullbacks (module
   `Submission.Work.A14D.LC_A_defs`): `∂_y^k(HU + HL∘w)` for the four `G`-slots, the primitive of
   `y'(G^{SU} − jets)/y^i` for the three integral slots, and the (disc-series) continuation of the
   pure pullbacks.
2. `JFA D : Fin 14 → ℂ → ℂ`, the *jump* of the fourteen pullbacks: `∂_y^k(D − D∘w)` for the
   `G`-slots, the primitive of `y'(D − D∘w)/y^i` for the integral slots, and
   `BUp j − (BUp j)∘w` for the pure slots.
3. `Ψ := Σᵢ pᵢ(y(·))·BU i ≡ 0` on `SU` (this is `Work.A14D.SU_relation_two`, from the disc
   relation `pullback_rel_disc_A` by the identity theorem on the convex `SU`), and the
   identification `JFA i = BU i − (BU i)∘w` on the wedge `SU ∩ SL` (proved for the `G`-slots by
   `Work.A14D.jump_G_ident`; the pure slots are definitional; the integral slots need the matching
   constant at the base point `cSU`).  Hence `LF := Σᵢ pᵢ(y(·))·JFA i` vanishes on the wedge, hence
   (identity theorem on the connected `Om1 ∖ {2}`) on all of `Om1`, hence on `halfU δ`.
4. The log decomposition of `LF` on `halfU δ`: its `log` coefficient is `κU · Xfun P y9 (jPrim y9)`
   (the slot bookkeeping `jumpCoeff_gIdx`/`jumpCoeff_iIdx`/`sum_jumpCoeff_eq` in this file), and
   the remainder has only a pole at `1/9`; pieces: `Work.A14D.decomp_G`, `Work.A14D.decomp_I`,
   and the (trivial-log-coefficient) pure part.
5. `Work.A14D.extract_log_half` gives `κU · Xfun ≡ 0`; the same argument on `halfL δ` (with
   `H_cont`/`D` mirrored by `−conj`) gives `κL · Xfun ≡ 0`.

Proved/available pieces (this session): `Work.A14D.extract_log_half` (here and in its own module),
`Work.A14D.pure_su_extension`, `Work.A14D.SU_relation` (proved by a colleague; stated with
analyticity on all of `SU`), `Work.A14D.LC_A_defs` (the definitions of `cSU`, `cSL`, `pureIdxA`,
`gIdxA`, `iIdxA`, `GjetA`, `BUg`, `BUi`, `BUp`, `BU`, `JFG`, `JFI`, `JFp`, `JFA`, `LF` together
with `BUp_eq_choose`, `BUp_analytic_SU`, `BUp_series`).

Delegated and running at hand-off: `Dw_extends`, `decomp_G`, `jump_G_ident`, `decomp_I`,
`BU_analytic_agree`, `SU_relation_two`, `jump_I_ident`.

The integral slots need their constant pinned down: `JFI D i` (primitive of `y'(D − D∘w)/y^i`
vanishing at `cSU`) is *not* equal to `BUi i − (BUi i)∘w` on the wedge for an arbitrary constant;
`JFIc a b c HU HL D i` (also in `LC_A_defs`) is `JFI` recentred so that the two agree at the fixed
wedge point `cWedge = 3 + i/10`, and `Work.A14D.jump_I_ident` (delegated) proves the identity on the
whole wedge.

Assembly (this file, once the pieces land): take `J := fun i => jPrim y9 (i : ℕ)` (`exists_J_aux`,
`jPrim_hasDerivAt`, `jPrim_ninth`), build `Ψ z := Σᵢ pAtY (P i) z * BU a b c HU HL i z`, get
`Ψ ≡ 0` on `SU ∖ {2}` from `SU_relation_two` + `BU_analytic_agree`, conclude `LFc ≡ 0` on the wedge
(the jump identifications), extend to `Om1` (identity theorem on the connected `Om1 ∖ {2}`), so
`LFc ≡ 0` on `halfU δ`; the decompositions `decomp_G`, `decomp_I`, `decomp_pure` turn `LFc` into
`κU * Xfun P y9 (jPrim y9) * log(· − 1/9) + B` with `B`'s `(· − 1/9)^m`-multiple holomorphic on
the ball; `extract_log_half` gives the first conjunct.  The second conjunct (`κL`) uses the same
argument on `halfL δ` (mirroring by `conj`/`wC`, cf. `Work.A14D.conjRefl_HU_eq_HL`).

**SESSION 7 FINDINGS — the route is now fully specified; all analytic pieces are delegated and
running.**

DEFINITIONS (module `Submission.Work.A14D.LC_A_defs`): `BU a b c HU HL : Fin 14 → ℂ → ℂ` is the
`SU`-branch of the fourteen pullbacks (`BUg HU HL k = DyIter k (HU + HL∘wC)` for the four `G`-slots,
`BUi` (primitive of `y' y^{-i}((HU+HL∘wC) - jets)` from `cSU`) for the three integral slots, `BUp j`
for the seven pure slots); `JFG D k = DyIter k (jumpH D)`; `JFI D i`, `JFIc a b c HU HL D i`;
`JFp j = BUp j - BUp j∘wC`; `JFAc`; `LFc`.  Write `BUsl i := BU a b c HU HL i ∘ wC` (NOT defined in
the module yet — define it locally in the assembly).  Then, ON THE WEDGE `SU ∩ SL`:

* `JFG D k = BUg HU HL k - BUg HU HL k ∘ wC` (`Work.A14D.jump_G_ident`, PROVED),
* `JFIc a b c HU HL D i = BUi a b c HU HL i - BUi a b c HU HL i ∘ wC`
  (`Work.A14D.jump_I_ident`, PROVED),
* `JFp j = BUp j - BUp j ∘ wC` (definitional),

so for
`T z := Σ_k pAtY (P (gIdxA k)) z * JFG D k z + Σ_i pAtY (P (iIdxA i)) z * JFIc a b c HU HL D i z
        + PJ z`
(where `PJ` is the pure part of `Work.A14D.pure_part_upper`, see below) we get `T = Σ_i pAtY (P i)·(BU i - BUsl i)
= Ψ z - Ψ (wC z)` on the wedge, with `Ψ := Σ_i pAtY (P i)·BU i`; and `Ψ ≡ 0` on `SU \ {2}`
(`Work.A14D.SU_relation_two`, PROVED, whose two hypotheses come from `Work.A14D.BU_analytic_agree`,
PROVED) while `wC z ∈ SU \ {2}` and `pAtY (P i) (wC z) = pAtY (P i) z` (since `yC ∘ wC = yC`), so

  **`T ≡ 0` on the wedge `SU ∩ SL` (excluding `2`).**

That identity extends: `T` is analytic on `(SU \ {2}) ∪ {im > 0}` (the `G`-slots and `PJ` on `Om1`,
the integral slots on the convex `SU` and on `{im > 0}`), which is open and preconnected
(`preconnected_SU_diff_two` + `{im>0}` convex, meeting at `i/4`), so `T ≡ 0` on `halfU δ`.

DECOMPOSITION on `halfU δ` (this is the whole point): with `Dw_extends` (`De = D∘w` on `halfU δ`,
holomorphic on the ball) and `hU`,
* `JFG D k = κU * DyIter k y9 * log(z - 1/9) + B_k`, `(z-1/9)^{m_k} B_k` holomorphic on the ball
  (`Work.A14D.decomp_G`, PROVED);
* `JFI D i = κU * jPrim y9 i * log + B_i` (same shape; `Work.A14D.decomp_I`, delegated/running);
  `JFIc = JFI + const`, so `JFIc = κU * jPrim y9 i * log + (B_i + const)`;
* `PJ = PB` on `halfU δ` with `(z-1/9)^m PB` holomorphic on the ball
  (`Work.A14D.pure_part_upper`, delegated/running).

Summing, `0 = T = κU * Xfun P y9 (jPrim y9 ·) * log(z - 1/9) + B` on `halfU δ` with
`(z-1/9)^{m} B` holomorphic on the ball, and `Work.A14D.extract_log_half` (in this file) gives
`κU * Xfun P y9 (jPrim y9 ·) = 0` on the ball — the FIRST conjunct (the target's expression
`Σ_k pAtY (P ⟨5+k⟩) z * DyIter k y9 z + Σ_i pAtY (P ⟨11+i⟩) z * J i z` is `Xfun P y9 J z` for
`J := fun i => jPrim y9 (i:ℕ)`; the slots `⟨5+k⟩`/`⟨11+i⟩` are `gIdxA k`/`iIdxA i`).

THE SECOND CONJUNCT (`κL`) is the exact mirror, with the L-side objects:
`T_L z := Σ_k pAtY (P (gIdxA k)) z * JFG D k z + Σ_i pAtY (P (iIdxA i)) z * (L-integral jump) + PJ`,
where the L-integral jump is the `primSeg`-from-`cSL` primitive of
`ζ ↦ dyC ζ * (yC ζ)^{-i} * jumpH D ζ`, recentred at `cWedge` so that it equals `BUi i - BUi i ∘ wC`
on the wedge (the difference of two primitives of the same integrand on the connected wedge is a
constant, so this is bookkeeping).  `T_L` is analytic on `(SL \ {2}) ∪ {im < 0}` (the `G`-slots and
`PJ` on `Om1`; the L-integral jump on `SL` and on `{im<0}`: for `z ∈ {im<0}`, `wC z ∈ {im>0} ⊆ Om1`,
so `D ∘ wC` is directly analytic there), which contains the wedge and `halfL δ`, so `T_L ≡ 0` on
`halfL δ`; its decomposition uses `LogCoeff … (halfL δ) D κL` (`hL`), `D ∘ wC` holomorphic on the
ball from the lower side (`Work.A14D.Dw_extends_L`, delegated/running), the L-mirrors
`Work.A14D.decomp_G_L` / `decomp_I_L` (delegated/running) and `Work.A14D.pure_part_lower`
(delegated/running).  Same extraction ⇒ `κL * Xfun … = 0`.

REMARK on `PJ` and `pure_part_upper/lower`: the pure jumps do NOT vanish on the wedge (the two
branches differ by the monodromy of the pure entries around `x = 1`), but their continuation to
`Om1` is analytic (the design's `pure_jump_regular`), and on the upper (resp. lower) half-disc its
restriction agrees with a function holomorphic on the ball after clearing a pole — so the pure part
contributes NO `log` coefficient at `1/9` and a legitimate `B`-term.

**SESSION 5 FINDINGS (kept for the record; the "blocked" conclusion is superseded above).**

**Remaining work (older plan).**  Step 4 (`LC_jump_package`) is the analytic crux: pullback convergence and
continuation to `SU, SL`, the regular-singular-point analysis of the four `G`-entries (forcing
`κ·∂_y^k y9`), the antiderivative analysis of the three integral entries, and the monodromy of the
seven pure pullbacks (via `Work.C7.g_form`, where the monodromy around `z = 1` is an explicit
*analytic* function, so no log coefficient arises).  Step 5 and 6 are elementary.
-/

namespace Work.A14D

open Complex Metric
open scoped Topology


open scoped BigOperators

/-! ## The three primitives `J_i` (the existential half of the conclusion) -/

private lemma yC_diffOn {c : ℂ} {r : ℝ} (h : (1:ℂ) ∉ ball c r) :
    DifferentiableOn ℂ yC (ball c r) := by
  unfold yC
  exact (differentiableOn_id.pow 2).div
    (differentiableOn_id.sub (differentiableOn_const 1))
    (fun z hz => sub_ne_zero.mpr (fun hz1 => h (by rwa [hz1] at hz)))

private lemma yC_ne {c : ℂ} {r : ℝ} (h0 : (0:ℂ) ∉ ball c r) (h1 : (1:ℂ) ∉ ball c r) :
    ∀ z ∈ ball c r, yC z ≠ 0 := by
  intro z hz hz0
  have hz1 : z ≠ 1 := fun hh => h1 (by rwa [hh] at hz)
  have h : z ^ 2 = 0 := by
    have hh := hz0
    rw [yC] at hh
    field_simp at hh
    simpa using hh
  have hz0' : z = 0 := sq_eq_zero_iff.mp h
  rw [hz0'] at hz
  exact h0 hz

private lemma dyC_diffOn {c : ℂ} {r : ℝ} (h : (1:ℂ) ∉ ball c r) :
    DifferentiableOn ℂ dyC (ball c r) := by
  unfold dyC
  exact ((differentiableOn_id.pow 2).sub (differentiableOn_const 2 |>.mul differentiableOn_id)).div
    ((differentiableOn_id.sub (differentiableOn_const 1)).pow 2)
    (fun z hz => pow_ne_zero 2 (sub_ne_zero.mpr (fun hh => h (by rwa [hh] at hz))))

/-- The three functions `J_i` of the conclusion exist: on the convex ball `ball (1/9) δ`
(which avoids the zero `0` of `yC` and the pole `1` of `yC, dyC`), each is the primitive of the
holomorphic function `y^{−i}·y'·y9`, normalised to vanish at `1/9`. -/
theorem exists_J_aux (y9 : ℂ → ℂ) {δ : ℝ} (hY : Y9 y9 δ) :
    ∃ J : Fin 3 → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (J i) (ball ninth δ)) ∧ (∀ i, J i ninth = 0) ∧
      ∀ i : Fin 3, ∀ z ∈ ball ninth δ,
        HasDerivAt (J i) ((yC z)⁻¹ ^ (i : ℕ) * dyC z * y9 z) z := by
  obtain ⟨hδpos, hδ20, hy9d, hy9ne, hy9ode⟩ := hY
  have h0 : (0:ℂ) ∉ ball ninth δ := by
    intro hmem
    have h := hmem
    rw [Metric.mem_ball, Complex.dist_eq, zero_sub] at h
    have hle : ‖ninth‖ = 1/9 := by norm_num [ninth]
    rw [norm_neg, hle] at h
    linarith
  have h1 : (1:ℂ) ∉ ball ninth δ := by
    intro hmem
    have h := hmem
    rw [Metric.mem_ball, Complex.dist_eq] at h
    have hle : ‖(1:ℂ) - ninth‖ = 8/9 := by norm_num [ninth]
    rw [hle] at h
    linarith
  have hYd : DifferentiableOn ℂ yC (ball ninth δ) := yC_diffOn h1
  have hYne : ∀ z ∈ ball ninth δ, yC z ≠ 0 := yC_ne h0 h1
  have hDd : DifferentiableOn ℂ dyC (ball ninth δ) := dyC_diffOn h1
  have hfun : ∀ i : Fin 3, DifferentiableOn ℂ
      (fun z => (yC z)⁻¹ ^ (i : ℕ) * dyC z * y9 z) (ball ninth δ) := by
    intro i
    have hinv : DifferentiableOn ℂ (fun z => (yC z)⁻¹) (ball ninth δ) := hYd.inv hYne
    exact ((hinv.pow (i : ℕ)).mul hDd).mul hy9d
  choose F hF using fun i : Fin 3 => (hfun i).isExactOn_ball
  refine ⟨fun i z => F i z - F i ninth, ?_, ?_, ?_⟩
  · intro i z hz
    exact ((hF i z hz).sub_const _).differentiableAt.differentiableWithinAt
  · intro i; ring
  · intro i z hz
    simpa using (hF i z hz).sub_const (F i ninth)


/-! ## The index bookkeeping for `jumpCoeff`

`gIdx k` is the index of `∂_y^k y9` (slot `5 + k`) and `iIdx i` the index of the `i`-th primitive
(slot `11 + i`) among the fourteen functions. -/

/-- The slot of the `G`-entry `∂_y^k y9` (`k < 4`). -/
def gIdx (k : Fin 4) : Fin 14 := ⟨5 + (k : ℕ), by omega⟩

/-- The slot of the `i`-th integral entry (`i < 3`). -/
def iIdx (i : Fin 3) : Fin 14 := ⟨11 + (i : ℕ), by omega⟩

/-- `jumpCoeff` on the four `G`-slots is the `log`-coefficient `κ·∂_y^k y9`. -/
lemma jumpCoeff_gIdx (κ : ℂ) (y9 : ℂ → ℂ) (k : Fin 4) (z : ℂ) :
    jumpCoeff κ y9 (gIdx k) z = κ * DyIter (k : ℕ) y9 z := by
  unfold jumpCoeff gIdx
  rw [dif_pos (show 5 ≤ 5 + (k : ℕ) ∧ 5 + (k : ℕ) ≤ 8 by omega)]
  simp only [Fin.val_mk]
  congr 2
  omega

/-- `jumpCoeff` on the three integral slots is `κ` times the corresponding primitive. -/
lemma jumpCoeff_iIdx (κ : ℂ) (y9 : ℂ → ℂ) (i : Fin 3) (z : ℂ) :
    jumpCoeff κ y9 (iIdx i) z = κ * jPrim y9 (i : ℕ) z := by
  unfold jumpCoeff iIdx
  rw [dif_neg (show ¬ (5 ≤ 11 + (i : ℕ) ∧ 11 + (i : ℕ) ≤ 8) by omega)]
  rw [dif_pos (show 11 ≤ 11 + (i : ℕ) by omega)]
  simp only [Fin.val_mk]
  congr 2
  omega

/-- The `log`-structured relation restricted to the two slots: the `G`-block and the integral
block, expressed through `jumpCoeff`. -/
theorem sum_jumpCoeff_eq (κ : ℂ) (y9 : ℂ → ℂ) {J : Fin 3 → ℂ → ℂ} {P : Fin 14 → Polynomial ℚ}
    (z : ℂ) (hJ : ∀ i : Fin 3, J i z = jPrim y9 (i : ℕ) z) :
    (∑ k : Fin 4, pAtY (P (gIdx k)) z * jumpCoeff κ y9 (gIdx k) z)
        + (∑ i : Fin 3, pAtY (P (iIdx i)) z * jumpCoeff κ y9 (iIdx i) z)
      = κ * ((∑ k : Fin 4, pAtY (P (gIdx k)) z * DyIter (k : ℕ) y9 z)
        + (∑ i : Fin 3, pAtY (P (iIdx i)) z * J i z)) := by
  have h1 : (∑ k : Fin 4, pAtY (P (gIdx k)) z * jumpCoeff κ y9 (gIdx k) z)
      = κ * (∑ k : Fin 4, pAtY (P (gIdx k)) z * DyIter (k : ℕ) y9 z) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [jumpCoeff_gIdx]; ring)
  have h2 : (∑ i : Fin 3, pAtY (P (iIdx i)) z * jumpCoeff κ y9 (iIdx i) z)
      = κ * (∑ i : Fin 3, pAtY (P (iIdx i)) z * J i z) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [jumpCoeff_iIdx, ← hJ i]; ring)
  rw [h1, h2, mul_add]

/-- The `(LC)` expression of the target lemma: the `G`-block `Σ_k p_k(y(z))·∂_y^k y9(z)` plus
the integral block `Σ_i q_i(y(z))·J_i(z)`. -/
noncomputable def Xfun (P : Fin 14 → Polynomial ℚ) (y9 : ℂ → ℂ) (J : Fin 3 → ℂ → ℂ) (z : ℂ) : ℂ :=
  (∑ k : Fin 4, pAtY (P (gIdx k)) z * DyIter (k : ℕ) y9 z)
    + (∑ i : Fin 3, pAtY (P (iIdx i)) z * J i z)

/-! ## Uniqueness of the primitives of `y^{-i} y' y9` -/

/-- Two functions with the same `HasDerivAt` derivative `(yC ·)^{-i}·dyC·y9` on the ball
(convex, hence preconnected) and the same value at the centre `1/9` are equal.  This is what
identifies the `J i` of the conclusion with the canonical primitives `jPrim y9 i`. -/
theorem prim_unique {y9 : ℂ → ℂ} {δ : ℝ} (hY : Y9 y9 δ) {j : ℕ} {J K : ℂ → ℂ}
    (hJ : ∀ z ∈ ball ninth δ, HasDerivAt J ((yC z)⁻¹ ^ j * dyC z * y9 z) z)
    (hJ0 : J ninth = 0)
    (hK : ∀ z ∈ ball ninth δ, HasDerivAt K ((yC z)⁻¹ ^ j * dyC z * y9 z) z)
    (hK0 : K ninth = 0) :
    ∀ z ∈ ball ninth δ, J z = K z := by
  obtain ⟨hδpos, -⟩ := hY
  have hJd : DifferentiableOn ℂ J (ball ninth δ) :=
    fun z hz => (hJ z hz).differentiableAt.differentiableWithinAt
  have hKd : DifferentiableOn ℂ K (ball ninth δ) :=
    fun z hz => (hK z hz).differentiableAt.differentiableWithinAt
  refine Metric.isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected hJd hKd
    (fun z hz => by rw [(hJ z hz).deriv, (hK z hz).deriv])
    (Metric.mem_ball_self hδpos) (by rw [hJ0, hK0])

/-! ## The extraction of the `log`-coefficient -/

/-- **The extraction step.**  If `A` is holomorphic on the ball around `1/9`, `B` is
holomorphic on the punctured ball, and `A(z)·log (z − 1/9) + B(z) = 0` off the real axis
(i.e. on both half discs, since the principal logarithm is holomorphic there), then `A` vanishes
on the whole ball.  This is `log_structured_vanishes` in the form used by the `(LC)` transfer. -/
theorem logcoeff_zero_of_halfs {δ : ℝ} (hδ : 0 < δ) {A B : ℂ → ℂ}
    (hA : DifferentiableOn ℂ A (ball ninth δ))
    (hB : DifferentiableOn ℂ B (ball ninth δ \ {ninth}))
    (hid : ∀ z ∈ ball ninth δ, z.im ≠ 0 → A z * Complex.log (z - ninth) + B z = 0) :
    ∀ z ∈ ball ninth δ, A z = 0 :=
  log_structured_vanishes hδ hA hB hid


/-! ## The one-sided extraction with a pole-type remainder

This is the form of the extraction actually used by the `(LC)` transfer: the identity
`A z * log (z − 1/9) + B z = 0` only has to hold on the *upper* half of the disc, and the
remainder `B` is allowed to have a pole at `1/9` (a `log`-type singularity is excluded).  Clearing
the pole by multiplying with `(z − 1/9)^m` turns it into an identity on the upper half disc with
both `Â = (z − 1/9)^m A` and `B̂ = (z − 1/9)^m B` holomorphic on the whole disc; the identity then
propagates to the lower half disc (across the real axis at points `> 1/9`, where the principal
logarithm is holomorphic) by `Dzc_log_structured_extend`, and the two-sided extraction
`logcoeff_zero_of_halfs` finishes. -/

theorem extract_log_half {δ : ℝ} (hδ : 0 < δ) {A B : ℂ → ℂ} (m : ℕ)
    (hA : DifferentiableOn ℂ A (ball ninth δ))
    (hB : DifferentiableOn ℂ (fun z => (z - ninth) ^ m * B z) (ball ninth δ))
    (hid : ∀ z ∈ halfU δ, A z * Complex.log (z - ninth) + B z = 0) :
    ∀ z ∈ ball ninth δ, A z = 0 := by
  set Ah : ℂ → ℂ := fun z => (z - ninth) ^ m * A z with hAhdef
  set Bh : ℂ → ℂ := fun z => (z - ninth) ^ m * B z with hBhdef
  have hAh : DifferentiableOn ℂ Ah (ball ninth δ) := by
    rw [hAhdef]
    exact ((differentiableOn_id.sub (differentiableOn_const ninth)).pow m).mul hA
  have hid' : ∀ z ∈ halfU δ, Ah z * Complex.log (z - ninth) + Bh z = 0 := by
    intro z hz
    have h := hid z hz
    rw [hAhdef, hBhdef]
    calc (z - ninth) ^ m * A z * Complex.log (z - ninth) + (z - ninth) ^ m * B z
        = (z - ninth) ^ m * (A z * Complex.log (z - ninth) + B z) := by ring
      _ = 0 := by rw [h, mul_zero]
  have hBpunct : DifferentiableOn ℂ Bh (ball ninth δ \ {ninth}) :=
    hB.mono (Set.sdiff_subset)
  have hext : ∀ z ∈ ball ninth δ, z.im ≠ 0 →
      Ah z * Complex.log (z - ninth) + Bh z = 0 :=
    Dzc_log_structured_extend hδ hAh hBpunct hid'
  have hzero : ∀ z ∈ ball ninth δ, Ah z = 0 :=
    logcoeff_zero_of_halfs hδ hAh hBpunct hext
  have hA0 : ∀ z ∈ ball ninth δ, z ≠ ninth → A z = 0 := by
    intro z hz hzne
    have h := hzero z hz
    rw [hAhdef] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero m (sub_ne_zero.mpr hzne))
  intro z hz
  by_cases hzne : z = ninth
  · subst hzne
    have hcont : ContinuousAt A ninth :=
      hA.continuousOn.continuousAt (Metric.ball_mem_nhds ninth hδ)
    have heq0 : (fun z : ℂ => A z) =ᶠ[𝓝[≠] ninth] 0 := by
      rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds ninth hδ] with z hzball hzne'
      exact hA0 z hzball (by simpa using hzne')
    have hlim0 : Filter.Tendsto A (𝓝[≠] ninth) (𝓝 0) :=
      Filter.Tendsto.congr' heq0.symm tendsto_const_nhds
    have hlimA : Filter.Tendsto A (𝓝[≠] ninth) (𝓝 (A ninth)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique hlimA hlim0
  · exact hA0 z hz hzne

/-! ## The canonical primitives `jPrim y9 i`

`jPrim y9 j = primSeg (fun z => (yC z)⁻¹ ^ j * dyC z * y9 z) ninth` is the segment primitive
vanishing at `1/9` of the integrand appearing in the conclusion; these lemmas identify it with the
functions produced by `exists_J_aux` (via `prim_unique`). -/

/-- `jPrim y9 i` vanishes at the centre `1/9`. -/
theorem jPrim_ninth (y9 : ℂ → ℂ) (i : ℕ) : jPrim y9 i ninth = 0 := by
  rw [jPrim, primSeg]
  simp

/-! ## Helpers for the assembly of the `(LC)` transfer

These are elementary facts used only here: the `wC`-invariance of `pAtY`, the holomorphy of the
jump functions `JFG D k` (on the half planes) and of the integral jumps `JFI D i`, `JFI_L D i`
(on the convex half planes `SU`, `SL` and the two open half planes), and the two connectedness
statements used in the identity-theorem steps. -/

/-- `yC (wC z) = yC z`; this is why `pAtY p` is `wC`-invariant. -/
private lemma yC_wC_eq {z : ℂ} (hz : z ≠ 1) : yC (wC z) = yC z := by
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have h1 : wC z - 1 = (z - 1)⁻¹ := by
    simp only [wC]; field_simp; ring
  have h2 : wC z = z * (z - 1)⁻¹ := by simp only [wC, div_eq_mul_inv]
  rw [yC, yC, h1, h2]
  field_simp

/-- `pAtY p` is `wC`-invariant. -/
private lemma pAtY_wC_eq (p : Polynomial ℚ) {z : ℂ} (hz : z ≠ 1) :
    pAtY p (wC z) = pAtY p z := by
  simp only [pAtY, yC_wC_eq hz]

/-- `pAtY p` is holomorphic off the pole `1` of `yC`. -/
private lemma pAtY_diffOn (p : Polynomial ℚ) {S : Set ℂ} (hS : (1 : ℂ) ∉ S) :
    DifferentiableOn ℂ (pAtY p) S := by
  have hyC : DifferentiableOn ℂ yC S := by
    unfold yC
    exact (differentiableOn_id.pow 2).div (differentiableOn_id.sub (differentiableOn_const 1))
      (fun z hz => sub_ne_zero.mpr (fun h => hS (by rwa [h] at hz)))
  have h : pAtY p = fun z => (p.map (algebraMap ℚ ℂ)).eval (yC z) := by
    funext z; rw [pAtY, Polynomial.eval₂_eq_eval_map]
  rw [h]
  exact (Polynomial.differentiable (p.map (algebraMap ℚ ℂ))).differentiableOn.comp hyC
    (fun _ _ => Set.mem_univ _)

/-- The real and imaginary parts of `wC z = 1 + (z − 1)⁻¹`. -/
private lemma wC_re_im {z : ℂ} (hz : z ≠ 1) :
    (wC z).re = 1 + (z.re - 1) / Complex.normSq (z - 1) ∧
      (wC z).im = -(z.im) / Complex.normSq (z - 1) := by
  have hw : wC z = 1 + (z - 1)⁻¹ := by
    have h : wC z - 1 = (z - 1)⁻¹ := by simp only [wC]; field_simp; ring
    rw [← h]; ring
  constructor
  · rw [hw]
    simp only [Complex.add_re, Complex.one_re, Complex.inv_re, Complex.sub_re]
    try ring
  · rw [hw]
    simp only [Complex.add_im, Complex.one_im, Complex.inv_im, Complex.sub_im]
    try ring

/-- `wC` maps the half plane `SU` into `SL`. -/
private lemma wC_mem_SL_of_mem_SU {z : ℂ} (hz : z ∈ SU) : wC z ∈ SL := by
  have hz1 : z ≠ 1 := fun h => one_notMem_SU (h ▸ hz)
  have hz' : 1 < 8 * z.im + z.re := mem_SU_iff.mp hz
  have hN : 0 < Complex.normSq (z - 1) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hz1)
  obtain ⟨hr, hi⟩ := wC_re_im hz1
  rw [mem_SL_iff, ← sub_pos]
  have hkey : (wC z).re - (8 * (wC z).im + 1)
      = (8 * z.im + z.re - 1) / Complex.normSq (z - 1) := by
    rw [hr, hi]; field_simp; ring
  rw [hkey, div_pos_iff_of_pos_right hN]
  linarith

/-- `wC` maps the half plane `SL` into `SU`. -/
private lemma wC_mem_SU_of_mem_SL {z : ℂ} (hz : z ∈ SL) : wC z ∈ SU := by
  have hz1 : z ≠ 1 := fun h => one_notMem_SL (h ▸ hz)
  have hz' : 8 * z.im + 1 < z.re := mem_SL_iff.mp hz
  have hN : 0 < Complex.normSq (z - 1) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hz1)
  obtain ⟨hr, hi⟩ := wC_re_im hz1
  rw [mem_SU_iff, ← sub_pos]
  have hkey : 8 * (wC z).im + (wC z).re - 1
      = (z.re - 1 - 8 * z.im) / Complex.normSq (z - 1) := by
    rw [hr, hi]; field_simp; ring
  rw [hkey, div_pos_iff_of_pos_right hN]
  linarith

private lemma cSU_mem_SU : cSU ∈ SU := by rw [mem_SU_iff]; norm_num [cSU]
private lemma cSL_mem_SL : cSL ∈ SL := by rw [mem_SL_iff]; norm_num [cSL]

/-- `wC` maps the lower half plane into the upper one. -/
private lemma wC_im_pos_of_neg_aux {z : ℂ} (hz : z.im < 0) : 0 < (wC z).im := by
  have hz1 : z ≠ 1 := fun h => by rw [h] at hz; norm_num at hz
  have hN : 0 < Complex.normSq (z - 1) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hz1)
  obtain ⟨-, hi⟩ := wC_re_im hz1
  rw [hi]
  exact div_pos (by linarith) hN

/-- `wC` is holomorphic off `1`. -/
private lemma wC_diffOn_of_notMem_one {S : Set ℂ} (h1 : (1 : ℂ) ∉ S) :
    DifferentiableOn ℂ wC S := by
  unfold wC
  exact differentiableOn_id.div (differentiableOn_id.sub (differentiableOn_const 1))
    (fun z hz => sub_ne_zero.mpr (fun h => h1 (by rwa [h] at hz)))

/-- The jump `jumpH D = D − D∘wC` is holomorphic on a set whose points and whose `wC`-images lie
in the slit plane `Om1`. -/
private lemma jumpH_diffOn {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) {S : Set ℂ}
    (hS : ∀ z ∈ S, z ∈ Om1) (hwS : ∀ z ∈ S, wC z ∈ Om1) (h1 : (1 : ℂ) ∉ S) :
    DifferentiableOn ℂ (jumpH D) S := by
  have hcomp : DifferentiableOn ℂ (fun z => D (wC z)) S :=
    hD.comp (wC_diffOn_of_notMem_one h1) hwS
  rw [show jumpH D = fun z => D z - D (wC z) from rfl]
  exact (hD.mono hS).sub hcomp

/-- The integrand `jIntJ D j = y'·y^{−j}·(D − D∘wC)` of the integral jumps is holomorphic on a
set avoiding `0` and `1` whose points and `wC`-images lie in `Om1`. -/
private lemma jIntJ_diffOn {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (j : ℕ) {S : Set ℂ}
    (hS : ∀ z ∈ S, z ∈ Om1) (hwS : ∀ z ∈ S, wC z ∈ Om1) (h1 : (1 : ℂ) ∉ S)
    (h0 : (0 : ℂ) ∉ S) : DifferentiableOn ℂ (jIntJ D j) S := by
  have hyC : DifferentiableOn ℂ yC S := by
    unfold yC
    exact (differentiableOn_id.pow 2).div (differentiableOn_id.sub (differentiableOn_const 1))
      (fun z hz => sub_ne_zero.mpr (fun h => h1 (by rwa [h] at hz)))
  have hne : ∀ z ∈ S, yC z ≠ 0 := by
    intro z hz hy
    have hz1 : z ≠ 1 := fun h => h1 (h ▸ hz)
    have h2 : z ^ 2 = 0 := by
      have hh := hy
      simp only [yC] at hh
      field_simp at hh
      simpa using hh
    have hz0 : z = 0 := sq_eq_zero_iff.mp h2
    exact h0 (hz0 ▸ hz)
  have hdyC : DifferentiableOn ℂ dyC S := by
    unfold dyC
    exact ((differentiableOn_id.pow 2).sub
        (differentiableOn_const 2 |>.mul differentiableOn_id)).div
      ((differentiableOn_id.sub (differentiableOn_const 1)).pow 2)
      (fun z hz => pow_ne_zero 2 (sub_ne_zero.mpr (fun h => h1 (by rwa [h] at hz))))
  rw [show jIntJ D j = fun z => dyC z * (yC z)⁻¹ ^ j * jumpH D z from rfl]
  exact (hdyC.mul ((hyC.inv hne).pow j)).mul (jumpH_diffOn hD hS hwS h1)

/-- The open upper half plane. -/
private def UHalf : Set ℂ := {z : ℂ | 0 < z.im}

/-- The open lower half plane. -/
private def LHalf : Set ℂ := {z : ℂ | z.im < 0}

private lemma isOpen_UHalf : IsOpen UHalf := isOpen_lt continuous_const Complex.continuous_im
private lemma isOpen_LHalf : IsOpen LHalf := isOpen_lt Complex.continuous_im continuous_const
private lemma convex_UHalf : Convex ℝ UHalf := convex_halfSpace_im_gt 0
private lemma convex_LHalf : Convex ℝ LHalf := convex_halfSpace_im_lt 0
private lemma cSU_mem_UHalf : cSU ∈ UHalf := by norm_num [UHalf, cSU]
private lemma cSL_mem_LHalf : cSL ∈ LHalf := by norm_num [LHalf, cSL]
private lemma one_notMem_UHalf : (1 : ℂ) ∉ UHalf := by norm_num [UHalf]
private lemma zero_notMem_UHalf : (0 : ℂ) ∉ UHalf := by norm_num [UHalf]
private lemma one_notMem_LHalf : (1 : ℂ) ∉ LHalf := by norm_num [LHalf]
private lemma zero_notMem_LHalf : (0 : ℂ) ∉ LHalf := by norm_num [LHalf]

private lemma jIntJ_diffOn_SU {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (j : ℕ) :
    DifferentiableOn ℂ (jIntJ D j) SU :=
  jIntJ_diffOn hD j (fun z hz => SU_subset_Om1 hz)
    (fun z hz => SL_subset_Om1 (wC_mem_SL_of_mem_SU hz)) one_notMem_SU zero_notMem_SU

private lemma jIntJ_diffOn_SL {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (j : ℕ) :
    DifferentiableOn ℂ (jIntJ D j) SL :=
  jIntJ_diffOn hD j (fun z hz => SL_subset_Om1 hz)
    (fun z hz => SU_subset_Om1 (wC_mem_SU_of_mem_SL hz)) one_notMem_SL zero_notMem_SL

private lemma jIntJ_diffOn_UHalf {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (j : ℕ) :
    DifferentiableOn ℂ (jIntJ D j) UHalf :=
  jIntJ_diffOn hD j (fun z hz => Or.inl (ne_of_gt hz))
    (fun z hz => Or.inl (ne_of_lt (wC_im_neg hz))) one_notMem_UHalf zero_notMem_UHalf

private lemma jIntJ_diffOn_LHalf {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (j : ℕ) :
    DifferentiableOn ℂ (jIntJ D j) LHalf :=
  jIntJ_diffOn hD j (fun z hz => Or.inl (ne_of_lt hz))
    (fun z hz => Or.inl (ne_of_gt (wC_im_pos_of_neg_aux hz))) one_notMem_LHalf zero_notMem_LHalf

/-- `JFI D i` (the primitive of `jIntJ D i` based at `cSU`) is holomorphic on `SU`. -/
private lemma JFI_diffOn_SU {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (i : Fin 3) :
    DifferentiableOn ℂ (JFI D i) SU := by
  have hf : DifferentiableOn ℂ (jIntJ D (i : ℕ)) SU := jIntJ_diffOn_SU hD (i : ℕ)
  rw [JFI_eq_primSeg]
  intro z hz
  exact (primSeg_hasDerivAt convex_SU isOpen_SU_H_cont cSU_mem_SU hf z hz).differentiableAt
    |>.differentiableWithinAt

/-- `JFI D i` is holomorphic on the open upper half plane. -/
private lemma JFI_diffOn_UHalf {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (i : Fin 3) :
    DifferentiableOn ℂ (JFI D i) UHalf := by
  have hf : DifferentiableOn ℂ (jIntJ D (i : ℕ)) UHalf := jIntJ_diffOn_UHalf hD (i : ℕ)
  rw [JFI_eq_primSeg]
  intro z hz
  exact (primSeg_hasDerivAt convex_UHalf isOpen_UHalf cSU_mem_UHalf hf z hz).differentiableAt
    |>.differentiableWithinAt

/-- `JFI_L D i` (the primitive of `jIntJ D i` based at `cSL`) is holomorphic on `SL`. -/
private lemma JFI_L_diffOn_SL {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (i : Fin 3) :
    DifferentiableOn ℂ (JFI_L D i) SL := by
  have hf : DifferentiableOn ℂ (jIntJ D (i : ℕ)) SL := jIntJ_diffOn_SL hD (i : ℕ)
  have h : JFI_L D i = primSeg (jIntJ D (i : ℕ)) cSL := rfl
  rw [h]
  intro z hz
  exact (primSeg_hasDerivAt convex_SL isOpen_SL_H_cont cSL_mem_SL hf z hz).differentiableAt
    |>.differentiableWithinAt

/-- `JFI_L D i` is holomorphic on the open lower half plane. -/
private lemma JFI_L_diffOn_LHalf {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (i : Fin 3) :
    DifferentiableOn ℂ (JFI_L D i) LHalf := by
  have hf : DifferentiableOn ℂ (jIntJ D (i : ℕ)) LHalf := jIntJ_diffOn_LHalf hD (i : ℕ)
  have h : JFI_L D i = primSeg (jIntJ D (i : ℕ)) cSL := rfl
  rw [h]
  intro z hz
  exact (primSeg_hasDerivAt convex_LHalf isOpen_LHalf cSL_mem_LHalf hf z hz).differentiableAt
    |>.differentiableWithinAt

/-- `JFG D k = ∂_y^k (D − D∘wC)` is holomorphic on `SU ∖ {2}`. -/
private lemma JFG_diffOn_SU {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (k : ℕ) :
    DifferentiableOn ℂ (JFG D k) (SU \ ({2} : Set ℂ)) := by
  have hopen : IsOpen (SU \ ({2} : Set ℂ)) := isOpen_SU_H_cont.sdiff isClosed_singleton
  have hj : DifferentiableOn ℂ (jumpH D) (SU \ ({2} : Set ℂ)) :=
    jumpH_diffOn hD (fun z hz => SU_subset_Om1 hz.1)
      (fun z hz => SL_subset_Om1 (wC_mem_SL_of_mem_SU hz.1)) (fun h => one_notMem_SU h.1)
  exact DyIter_diffOn_of_isOpen hopen (fun h => zero_notMem_SU h.1) (by simp) hj k

/-- `JFG D k` is holomorphic on the open upper half plane. -/
private lemma JFG_diffOn_UHalf {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (k : ℕ) :
    DifferentiableOn ℂ (JFG D k) UHalf := by
  have hj : DifferentiableOn ℂ (jumpH D) UHalf :=
    jumpH_diffOn hD (fun z hz => Or.inl (ne_of_gt hz))
      (fun z hz => Or.inl (ne_of_lt (wC_im_neg hz))) one_notMem_UHalf
  exact DyIter_diffOn_of_isOpen isOpen_UHalf zero_notMem_UHalf one_notMem_UHalf hj k

/-- `JFG D k` is holomorphic on `SL ∖ {2}`. -/
private lemma JFG_diffOn_SL {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (k : ℕ) :
    DifferentiableOn ℂ (JFG D k) (SL \ ({2} : Set ℂ)) := by
  have hopen : IsOpen (SL \ ({2} : Set ℂ)) := isOpen_SL_H_cont.sdiff isClosed_singleton
  have hj : DifferentiableOn ℂ (jumpH D) (SL \ ({2} : Set ℂ)) :=
    jumpH_diffOn hD (fun z hz => SL_subset_Om1 hz.1)
      (fun z hz => SU_subset_Om1 (wC_mem_SU_of_mem_SL hz.1)) (fun h => one_notMem_SL h.1)
  exact DyIter_diffOn_of_isOpen hopen (fun h => zero_notMem_SL h.1) (by simp) hj k

/-- `JFG D k` is holomorphic on the open lower half plane. -/
private lemma JFG_diffOn_LHalf {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (k : ℕ) :
    DifferentiableOn ℂ (JFG D k) LHalf := by
  have hj : DifferentiableOn ℂ (jumpH D) LHalf :=
    jumpH_diffOn hD (fun z hz => Or.inl (ne_of_lt hz))
      (fun z hz => Or.inl (ne_of_gt (wC_im_pos_of_neg_aux hz))) one_notMem_LHalf
  exact DyIter_diffOn_of_isOpen isOpen_LHalf zero_notMem_LHalf one_notMem_LHalf hj k

/-- The connectedness of the region used for the `SU`-side identity theorem. -/
private lemma preconnected_SU_union_UHalf :
    IsPreconnected ((SU \ ({2} : Set ℂ)) ∪ UHalf) := by
  refine IsPreconnected.union ((1 / 4 : ℂ) * Complex.I) ?_ ?_ preconnected_SU_diff_two
    convex_UHalf.isPreconnected
  · refine ⟨?_, ?_⟩
    · rw [mem_SU_iff]; norm_num
    · intro h; have := congrArg Complex.im h; norm_num at this
  · show 0 < ((1 / 4 : ℂ) * Complex.I).im; norm_num

/-- `wC` maps the punctured half plane `SU ∖ {2}` onto `SL ∖ {2}`. -/
private lemma wC_image_SU_sdiff :
    wC '' (SU \ ({2} : Set ℂ)) = SL \ ({2} : Set ℂ) := by
  have h2 : ∀ z : ℂ, z ≠ 1 → (wC z = 2 ↔ z = 2) := by
    intro z hz
    constructor
    · intro h
      rw [← wC_wC z hz, h]; norm_num [wC]
    · intro h; rw [h]; norm_num [wC]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hwSU, hw2⟩ := hw
    have hw1 : w ≠ 1 := fun h => one_notMem_SU (h ▸ hwSU)
    exact ⟨wC_mem_SL_of_mem_SU hwSU, fun h => hw2 ((h2 w hw1).mp (by simpa using h))⟩
  · intro hz
    obtain ⟨hzSL, hz2⟩ := hz
    have hz1 : z ≠ 1 := fun h => one_notMem_SL (h ▸ hzSL)
    refine ⟨wC z, ⟨wC_mem_SU_of_mem_SL hzSL,
      fun h => hz2 ((h2 z hz1).mp (by simpa using h))⟩, wC_wC z hz1⟩

/-- `wC` maps the open upper half plane onto the open lower half plane. -/
private lemma wC_image_UHalf : wC '' UHalf = LHalf := by
  ext z; constructor
  · rintro ⟨w, hw, rfl⟩
    exact wC_im_neg hw
  · intro hz
    exact ⟨wC z, wC_im_pos_of_neg_aux hz, wC_wC z (fun h => one_notMem_LHalf (h ▸ hz))⟩

/-- The connectedness of the region used for the `SL`-side identity theorem. -/
private lemma preconnected_SL_union_LHalf :
    IsPreconnected ((SL \ ({2} : Set ℂ)) ∪ LHalf) := by
  have himg : (SL \ ({2} : Set ℂ)) ∪ LHalf
      = wC '' ((SU \ ({2} : Set ℂ)) ∪ UHalf) := by
    rw [Set.image_union, wC_image_SU_sdiff, wC_image_UHalf]
  have hcont : ContinuousOn wC ((SU \ ({2} : Set ℂ)) ∪ UHalf) := by
    intro z hz
    rcases hz with hz | hz
    · exact (differentiableAt_wC z (fun h => one_notMem_SU (h ▸ hz.1))).continuousAt
        |>.continuousWithinAt
    · exact (differentiableAt_wC z (fun h => one_notMem_UHalf (h ▸ hz))).continuousAt
        |>.continuousWithinAt
  rw [himg]
  exact IsPreconnected.image preconnected_SU_union_UHalf wC hcont



/-! ## The two combinations `TJU`, `TJL` of the jumps, their holomorphy and the wedge identity -/

/-- Differentiability is local: on the union of two *open* sets it is enough to check each of
them. -/
private lemma diffOn_open_union {f : ℂ → ℂ} {s t : Set ℂ} (hs : IsOpen s) (ht : IsOpen t)
    (h1 : DifferentiableOn ℂ f s) (h2 : DifferentiableOn ℂ f t) :
    DifferentiableOn ℂ f (s ∪ t) := by
  intro z hz
  rcases hz with hz | hz
  · exact (h1.differentiableAt (hs.mem_nhds hz)).differentiableWithinAt
  · exact (h2.differentiableAt (ht.mem_nhds hz)).differentiableWithinAt

private lemma UHalf_subset_Om1 : UHalf ⊆ Om1 := fun z hz => Or.inl (ne_of_gt hz)
private lemma LHalf_subset_Om1 : LHalf ⊆ Om1 := fun z hz => Or.inl (ne_of_lt hz)

/-- The fourteen slots split into the four `G`-slots, the three integral slots and the seven pure
slots. -/
private lemma sum_fin14_split (f : Fin 14 → ℂ) :
    ∑ i : Fin 14, f i
      = (∑ k : Fin 4, f (gIdxA k)) + (∑ i : Fin 3, f (iIdxA i))
        + (∑ j : Fin 7, f (pureIdxA j)) := by
  have hinj_g : Function.Injective gIdxA := by decide
  have hinj_i : Function.Injective iIdxA := by decide
  have hinj_p : Function.Injective pureIdxA := by decide
  have h1 : (Finset.univ : Finset (Fin 14)) =
      (Finset.univ.image gIdxA ∪ Finset.univ.image iIdxA ∪ Finset.univ.image pureIdxA) := by
    decide
  have hd1 : Disjoint (Finset.univ.image gIdxA) (Finset.univ.image iIdxA) := by decide
  have hd2 : Disjoint ((Finset.univ.image gIdxA) ∪ (Finset.univ.image iIdxA))
      (Finset.univ.image pureIdxA) := by decide
  conv_lhs => rw [h1]
  rw [Finset.sum_union hd2, Finset.sum_union hd1,
    Finset.sum_image (fun x _ y _ h => hinj_g h),
    Finset.sum_image (fun x _ y _ h => hinj_i h),
    Finset.sum_image (fun x _ y _ h => hinj_p h)]

private lemma BU_gIdxA (a b c : ℤ) (HU HL : ℂ → ℂ) (k : Fin 4) :
    BU a b c HU HL (gIdxA k) = BUg HU HL (k : ℕ) := by
  fin_cases k <;> rfl

private lemma BU_iIdxA (a b c : ℤ) (HU HL : ℂ → ℂ) (i : Fin 3) :
    BU a b c HU HL (iIdxA i) = BUi a b c HU HL i := by
  fin_cases i <;> rfl

private lemma BU_pureIdxA (a b c : ℤ) (HU HL : ℂ → ℂ) (j : Fin 7) :
    BU a b c HU HL (pureIdxA j) = BUp j := by
  fin_cases j <;> rfl

/-- `JFIc` is a primitive of `jIntJ` up to an additive constant. -/
private lemma JFIc_eq (a b c : ℤ) (HU HL D : ℂ → ℂ) (i : Fin 3) :
    JFIc a b c HU HL D i = fun z => ((BUi a b c HU HL i cWedge
      - BUi a b c HU HL i (wC cWedge)) - JFI D i cWedge) + JFI D i z := rfl

/-- `JFIc_L` is a primitive of `jIntJ` up to an additive constant. -/
private lemma JFIc_L_eq (a b c : ℤ) (HU HL D : ℂ → ℂ) (i : Fin 3) :
    JFIc_L a b c HU HL D i = fun z => ((BUi a b c HU HL i cWedge
      - BUi a b c HU HL i (wC cWedge)) - JFI_L D i cWedge) + JFI_L D i z := rfl

private lemma JFIc_diffOn_SU (a b c : ℤ) (HU HL D : ℂ → ℂ)
    (hD : DifferentiableOn ℂ D Om1) (i : Fin 3) :
    DifferentiableOn ℂ (JFIc a b c HU HL D i) SU := by
  rw [JFIc_eq]
  exact (differentiableOn_const _).add (JFI_diffOn_SU hD i)

private lemma JFIc_diffOn_UHalf (a b c : ℤ) (HU HL D : ℂ → ℂ)
    (hD : DifferentiableOn ℂ D Om1) (i : Fin 3) :
    DifferentiableOn ℂ (JFIc a b c HU HL D i) UHalf := by
  rw [JFIc_eq]
  exact (differentiableOn_const _).add (JFI_diffOn_UHalf hD i)

private lemma JFIc_L_diffOn_SL (a b c : ℤ) (HU HL D : ℂ → ℂ)
    (hD : DifferentiableOn ℂ D Om1) (i : Fin 3) :
    DifferentiableOn ℂ (JFIc_L a b c HU HL D i) SL := by
  rw [JFIc_L_eq]
  exact (differentiableOn_const _).add (JFI_L_diffOn_SL hD i)

private lemma JFIc_L_diffOn_LHalf (a b c : ℤ) (HU HL D : ℂ → ℂ)
    (hD : DifferentiableOn ℂ D Om1) (i : Fin 3) :
    DifferentiableOn ℂ (JFIc_L a b c HU HL D i) LHalf := by
  rw [JFIc_L_eq]
  exact (differentiableOn_const _).add (JFI_L_diffOn_LHalf hD i)

/-- The `SU`-side combination of the jump functions,
`Σ_k p_k·JFG_k + Σ_i q_i·JFIc_i + PJ`. -/
private noncomputable def TJU (a b c : ℤ) (HU HL D PJ : ℂ → ℂ) (P : Fin 14 → Polynomial ℚ) : ℂ → ℂ :=
  fun z => (∑ k : Fin 4, pAtY (P (gIdxA k)) z * JFG D (k : ℕ) z)
    + (∑ i : Fin 3, pAtY (P (iIdxA i)) z * JFIc a b c HU HL D i z) + PJ z

/-- The `SL`-side combination of the jump functions,
`Σ_k p_k·JFG_k + Σ_i q_i·JFIc_L_i + PJ`. -/
private noncomputable def TJL (a b c : ℤ) (HU HL D PJ : ℂ → ℂ) (P : Fin 14 → Polynomial ℚ) : ℂ → ℂ :=
  fun z => (∑ k : Fin 4, pAtY (P (gIdxA k)) z * JFG D (k : ℕ) z)
    + (∑ i : Fin 3, pAtY (P (iIdxA i)) z * JFIc_L a b c HU HL D i z) + PJ z

/-- `cWedge` lies in the punctured wedge. -/
private lemma cWedge_mem_wedge : cWedge ∈ (SU ∩ SL) \ ({2} : Set ℂ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mem_SU_iff]; norm_num [cWedge]
  · rw [mem_SL_iff]; norm_num [cWedge]
  · intro h
    have hre := congrArg Complex.re h
    norm_num [cWedge] at hre

private lemma JFI_L_eq_primSeg (D : ℂ → ℂ) (i : Fin 3) :
    JFI_L D i = primSeg (jIntJ D (i : ℕ)) cSL := rfl

/-- The two primitives `JFI_L` and `JFI` of the same integrand differ by a constant on the wedge
(which is convex, hence connected). -/
private lemma JFI_L_sub_JFI_const {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (i : Fin 3) :
    ∀ z ∈ SU ∩ SL, JFI_L D i z - JFI D i z = JFI_L D i cWedge - JFI D i cWedge := by
  have hdiff : DifferentiableOn ℂ (JFI_L D i - JFI D i) (SU ∩ SL) :=
    ((JFI_L_diffOn_SL hD i).mono Set.inter_subset_right).sub
      ((JFI_diffOn_SU hD i).mono Set.inter_subset_left)
  have hder : (SU ∩ SL).EqOn (deriv (JFI_L D i - JFI D i)) 0 := by
    intro z hz
    have hL : HasDerivAt (JFI_L D i) (jIntJ D (i : ℕ) z) z := by
      rw [JFI_L_eq_primSeg]
      exact primSeg_hasDerivAt convex_SL isOpen_SL_H_cont cSL_mem_SL (jIntJ_diffOn_SL hD (i : ℕ)) z hz.2
    have hU : HasDerivAt (JFI D i) (jIntJ D (i : ℕ) z) z := by
      rw [JFI_eq_primSeg]
      exact primSeg_hasDerivAt convex_SU isOpen_SU_H_cont cSU_mem_SU (jIntJ_diffOn_SU hD (i : ℕ)) z hz.1
    rw [(hL.sub hU).deriv]
    simp
  intro z hz
  exact IsOpen.is_const_of_deriv_eq_zero (isOpen_SU_H_cont.inter isOpen_SL_H_cont)
    (convex_SU.inter convex_SL).isPreconnected hdiff hder hz cWedge_mem_wedge.1

/-- **The `SL`-mirror of `jump_I_ident`.**  The recentred `L`-primitive `JFIc_L` agrees with
`BUi − (BUi)∘wC` on the wedge. -/
private lemma asm_jump_I_ident_L (a b c : ℤ) (HU HL D : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU) (hHL : DifferentiableOn ℂ HL SL)
    (hD : DifferentiableOn ℂ D Om1)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z) (i : Fin 3) :
    ∀ z ∈ SU ∩ SL, JFIc_L a b c HU HL D i z = BUi a b c HU HL i z - BUi a b c HU HL i (wC z) := by
  intro z hz
  have hK := JFI_L_sub_JFI_const hD i z hz
  have hK' : JFI_L D i z = (JFI_L D i cWedge - JFI D i cWedge) + JFI D i z :=
    sub_eq_iff_eq_add.mp hK
  have key : JFIc_L a b c HU HL D i z = JFIc a b c HU HL D i z := by
    have e1 : JFIc_L a b c HU HL D i z
        = ((BUi a b c HU HL i cWedge - BUi a b c HU HL i (wC cWedge)) - JFI_L D i cWedge)
          + JFI_L D i z := rfl
    have e2 : JFIc a b c HU HL D i z
        = ((BUi a b c HU HL i cWedge - BUi a b c HU HL i (wC cWedge)) - JFI D i cWedge)
          + JFI D i z := rfl
    rw [e1, e2, hK']
    ring
  rw [key, jump_I_ident a b c HU HL D hHU hHL hD hDj i z hz]

private lemma TJU_analytic {a b c : ℤ} {HU HL D PJ : ℂ → ℂ} {P : Fin 14 → Polynomial ℚ}
    (hD : DifferentiableOn ℂ D Om1) (hPJ : DifferentiableOn ℂ PJ Om1) :
    DifferentiableOn ℂ (TJU a b c HU HL D PJ P) ((SU \ ({2} : Set ℂ)) ∪ UHalf) := by
  have hSU : IsOpen (SU \ ({2} : Set ℂ)) := isOpen_SU_H_cont.sdiff isClosed_singleton
  have hGSU : DifferentiableOn ℂ
      (fun z => ∑ k : Fin 4, pAtY (P (gIdxA k)) z * JFG D (k : ℕ) z)
      (SU \ ({2} : Set ℂ)) :=
    DifferentiableOn.fun_sum fun k _ =>
      (pAtY_diffOn (P (gIdxA k)) (fun h => one_notMem_SU h.1)).mul (JFG_diffOn_SU hD (k : ℕ))
  have hGU : DifferentiableOn ℂ
      (fun z => ∑ k : Fin 4, pAtY (P (gIdxA k)) z * JFG D (k : ℕ) z) UHalf :=
    DifferentiableOn.fun_sum fun k _ =>
      (pAtY_diffOn (P (gIdxA k)) one_notMem_UHalf).mul (JFG_diffOn_UHalf hD (k : ℕ))
  have hISU : DifferentiableOn ℂ
      (fun z => ∑ i : Fin 3, pAtY (P (iIdxA i)) z * JFIc a b c HU HL D i z)
      (SU \ ({2} : Set ℂ)) :=
    DifferentiableOn.fun_sum fun i _ =>
      (pAtY_diffOn (P (iIdxA i)) (fun h => one_notMem_SU h.1)).mul
        ((JFIc_diffOn_SU a b c HU HL D hD i).mono Set.sdiff_subset)
  have hIU : DifferentiableOn ℂ
      (fun z => ∑ i : Fin 3, pAtY (P (iIdxA i)) z * JFIc a b c HU HL D i z) UHalf :=
    DifferentiableOn.fun_sum fun i _ =>
      (pAtY_diffOn (P (iIdxA i)) one_notMem_UHalf).mul
        (JFIc_diffOn_UHalf a b c HU HL D hD i)
  have hG := diffOn_open_union hSU isOpen_UHalf hGSU hGU
  have hI := diffOn_open_union hSU isOpen_UHalf hISU hIU
  have hPJ' := diffOn_open_union hSU isOpen_UHalf
    (hPJ.mono (fun z hz => SU_subset_Om1 hz.1)) (hPJ.mono UHalf_subset_Om1)
  exact (hG.add hI).add hPJ'

private lemma TJL_analytic {a b c : ℤ} {HU HL D PJ : ℂ → ℂ} {P : Fin 14 → Polynomial ℚ}
    (hD : DifferentiableOn ℂ D Om1) (hPJ : DifferentiableOn ℂ PJ Om1) :
    DifferentiableOn ℂ (TJL a b c HU HL D PJ P) ((SL \ ({2} : Set ℂ)) ∪ LHalf) := by
  have hSL : IsOpen (SL \ ({2} : Set ℂ)) := isOpen_SL_H_cont.sdiff isClosed_singleton
  have hGSL : DifferentiableOn ℂ
      (fun z => ∑ k : Fin 4, pAtY (P (gIdxA k)) z * JFG D (k : ℕ) z)
      (SL \ ({2} : Set ℂ)) :=
    DifferentiableOn.fun_sum fun k _ =>
      (pAtY_diffOn (P (gIdxA k)) (fun h => one_notMem_SL h.1)).mul (JFG_diffOn_SL hD (k : ℕ))
  have hGL : DifferentiableOn ℂ
      (fun z => ∑ k : Fin 4, pAtY (P (gIdxA k)) z * JFG D (k : ℕ) z) LHalf :=
    DifferentiableOn.fun_sum fun k _ =>
      (pAtY_diffOn (P (gIdxA k)) one_notMem_LHalf).mul (JFG_diffOn_LHalf hD (k : ℕ))
  have hISL : DifferentiableOn ℂ
      (fun z => ∑ i : Fin 3, pAtY (P (iIdxA i)) z * JFIc_L a b c HU HL D i z)
      (SL \ ({2} : Set ℂ)) :=
    DifferentiableOn.fun_sum fun i _ =>
      (pAtY_diffOn (P (iIdxA i)) (fun h => one_notMem_SL h.1)).mul
        ((JFIc_L_diffOn_SL a b c HU HL D hD i).mono Set.sdiff_subset)
  have hIL : DifferentiableOn ℂ
      (fun z => ∑ i : Fin 3, pAtY (P (iIdxA i)) z * JFIc_L a b c HU HL D i z) LHalf :=
    DifferentiableOn.fun_sum fun i _ =>
      (pAtY_diffOn (P (iIdxA i)) one_notMem_LHalf).mul
        (JFIc_L_diffOn_LHalf a b c HU HL D hD i)
  have hG := diffOn_open_union hSL isOpen_LHalf hGSL hGL
  have hI := diffOn_open_union hSL isOpen_LHalf hISL hIL
  have hPJ' := diffOn_open_union hSL isOpen_LHalf
    (hPJ.mono (fun z hz => SL_subset_Om1 hz.1)) (hPJ.mono LHalf_subset_Om1)
  exact (hG.add hI).add hPJ'

/-- The vanishing of the `SU`-side combination on the wedge. -/
private lemma TJU_wedge (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c)
    (P : Fin 14 → Polynomial ℚ)
    (hrel : ∑ i : Fin 14, (P i : PowerSeries ℚ) * Submission.CDTPlan.fourteen a b c i = 0)
    {HU HL D PJ : ℂ → ℂ}
    (hHU : DifferentiableOn ℂ HU SU) (hHL : DifferentiableOn ℂ HL SL)
    (hHUeq : ∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z)
    (hHLeq : ∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z)
    (hD : DifferentiableOn ℂ D Om1) (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z)
    (hPJ : ∀ z ∈ SU ∩ SL, PJ z
      = ∑ j : Fin 7, pAtY (P (pureIdxA j)) z * (BUp j z - BUp j (wC z))) :
    ∀ z ∈ (SU ∩ SL) \ ({2} : Set ℂ), TJU a b c HU HL D PJ P z = 0 := by
  have hBU := BU_analytic_agree a b c h HU HL hHU hHL hHUeq hHLeq
  have hPsi := SU_relation_two a b c h P hrel (BU a b c HU HL) hBU.1 hBU.2
  intro z hz
  obtain ⟨hzw, hz2⟩ := hz
  have hz1 : z ≠ 1 := fun h1 => one_notMem_SU (h1 ▸ hzw.1)
  have hzw' : wC z ∈ SU ∩ SL := wC_mem_SU_SL hzw
  have hwz2 : wC z ≠ 2 := by
    intro hh
    exact hz2 (by rw [← wC_wC z hz1, hh]; norm_num [wC])
  have hP1 : (∑ i : Fin 14, pAtY (P i) z * BU a b c HU HL i z) = 0 :=
    hPsi z ⟨hzw.1, by simpa using hz2⟩
  have hP2 : (∑ i : Fin 14, pAtY (P i) z * BU a b c HU HL i (wC z)) = 0 := by
    have h1 : (∑ i : Fin 14, pAtY (P i) z * BU a b c HU HL i (wC z))
        = ∑ i : Fin 14, pAtY (P i) (wC z) * BU a b c HU HL i (wC z) :=
      Finset.sum_congr rfl (fun i _ => by rw [pAtY_wC_eq (P i) hz1])
    rw [h1]
    exact hPsi (wC z) ⟨hzw'.1, by simpa using hwz2⟩
  have hsum : (∑ i : Fin 14,
      pAtY (P i) z * (BU a b c HU HL i z - BU a b c HU HL i (wC z))) = 0 := by
    have h1 : (∑ i : Fin 14,
        pAtY (P i) z * (BU a b c HU HL i z - BU a b c HU HL i (wC z)))
        = (∑ i : Fin 14, pAtY (P i) z * BU a b c HU HL i z)
          - (∑ i : Fin 14, pAtY (P i) z * BU a b c HU HL i (wC z)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [h1, hP1, hP2, sub_zero]
  have hsplit := sum_fin14_split (fun i : Fin 14 =>
    pAtY (P i) z * (BU a b c HU HL i z - BU a b c HU HL i (wC z)))
  rw [hsplit] at hsum
  have hG : (∑ k : Fin 4, pAtY (P (gIdxA k)) z
        * (BU a b c HU HL (gIdxA k) z - BU a b c HU HL (gIdxA k) (wC z)))
      = ∑ k : Fin 4, pAtY (P (gIdxA k)) z * JFG D (k : ℕ) z :=
    Finset.sum_congr rfl (fun k _ => by
      simp only [BU_gIdxA, BUg, JFG, jump_G_ident hHU hHL hDj (k : ℕ) z hzw])
  have hI : (∑ i : Fin 3, pAtY (P (iIdxA i)) z
        * (BU a b c HU HL (iIdxA i) z - BU a b c HU HL (iIdxA i) (wC z)))
      = ∑ i : Fin 3, pAtY (P (iIdxA i)) z * JFIc a b c HU HL D i z :=
    Finset.sum_congr rfl (fun i _ => by
      simp only [BU_iIdxA, ← jump_I_ident a b c HU HL D hHU hHL hD hDj i z hzw])
  have hP : (∑ j : Fin 7, pAtY (P (pureIdxA j)) z
        * (BU a b c HU HL (pureIdxA j) z - BU a b c HU HL (pureIdxA j) (wC z)))
      = ∑ j : Fin 7, pAtY (P (pureIdxA j)) z * (BUp j z - BUp j (wC z)) :=
    Finset.sum_congr rfl (fun j _ => by rw [BU_pureIdxA])
  rw [hG, hI, hP] at hsum
  rw [← hPJ z hzw] at hsum
  exact hsum

/-- The vanishing of the `SL`-side combination on the wedge. -/
private lemma TJL_wedge (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c)
    (P : Fin 14 → Polynomial ℚ)
    (hrel : ∑ i : Fin 14, (P i : PowerSeries ℚ) * Submission.CDTPlan.fourteen a b c i = 0)
    {HU HL D PJ : ℂ → ℂ}
    (hHU : DifferentiableOn ℂ HU SU) (hHL : DifferentiableOn ℂ HL SL)
    (hHUeq : ∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z)
    (hHLeq : ∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z)
    (hD : DifferentiableOn ℂ D Om1) (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z)
    (hPJ : ∀ z ∈ SU ∩ SL, PJ z
      = ∑ j : Fin 7, pAtY (P (pureIdxA j)) z * (BUp j z - BUp j (wC z))) :
    ∀ z ∈ (SU ∩ SL) \ ({2} : Set ℂ), TJL a b c HU HL D PJ P z = 0 := by
  have hBU := BU_analytic_agree a b c h HU HL hHU hHL hHUeq hHLeq
  have hPsi := SU_relation_two a b c h P hrel (BU a b c HU HL) hBU.1 hBU.2
  intro z hz
  obtain ⟨hzw, hz2⟩ := hz
  have hz1 : z ≠ 1 := fun h1 => one_notMem_SU (h1 ▸ hzw.1)
  have hzw' : wC z ∈ SU ∩ SL := wC_mem_SU_SL hzw
  have hwz2 : wC z ≠ 2 := by
    intro hh
    exact hz2 (by rw [← wC_wC z hz1, hh]; norm_num [wC])
  have hP1 : (∑ i : Fin 14, pAtY (P i) z * BU a b c HU HL i z) = 0 :=
    hPsi z ⟨hzw.1, by simpa using hz2⟩
  have hP2 : (∑ i : Fin 14, pAtY (P i) z * BU a b c HU HL i (wC z)) = 0 := by
    have h1 : (∑ i : Fin 14, pAtY (P i) z * BU a b c HU HL i (wC z))
        = ∑ i : Fin 14, pAtY (P i) (wC z) * BU a b c HU HL i (wC z) :=
      Finset.sum_congr rfl (fun i _ => by rw [pAtY_wC_eq (P i) hz1])
    rw [h1]
    exact hPsi (wC z) ⟨hzw'.1, by simpa using hwz2⟩
  have hsum : (∑ i : Fin 14,
      pAtY (P i) z * (BU a b c HU HL i z - BU a b c HU HL i (wC z))) = 0 := by
    have h1 : (∑ i : Fin 14,
        pAtY (P i) z * (BU a b c HU HL i z - BU a b c HU HL i (wC z)))
        = (∑ i : Fin 14, pAtY (P i) z * BU a b c HU HL i z)
          - (∑ i : Fin 14, pAtY (P i) z * BU a b c HU HL i (wC z)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [h1, hP1, hP2, sub_zero]
  have hsplit := sum_fin14_split (fun i : Fin 14 =>
    pAtY (P i) z * (BU a b c HU HL i z - BU a b c HU HL i (wC z)))
  rw [hsplit] at hsum
  have hG : (∑ k : Fin 4, pAtY (P (gIdxA k)) z
        * (BU a b c HU HL (gIdxA k) z - BU a b c HU HL (gIdxA k) (wC z)))
      = ∑ k : Fin 4, pAtY (P (gIdxA k)) z * JFG D (k : ℕ) z :=
    Finset.sum_congr rfl (fun k _ => by
      simp only [BU_gIdxA, BUg, JFG, jump_G_ident hHU hHL hDj (k : ℕ) z hzw])
  have hI : (∑ i : Fin 3, pAtY (P (iIdxA i)) z
        * (BU a b c HU HL (iIdxA i) z - BU a b c HU HL (iIdxA i) (wC z)))
      = ∑ i : Fin 3, pAtY (P (iIdxA i)) z * JFIc_L a b c HU HL D i z :=
    Finset.sum_congr rfl (fun i _ => by
      simp only [BU_iIdxA, ← asm_jump_I_ident_L a b c HU HL D hHU hHL hD hDj i z hzw])
  have hP : (∑ j : Fin 7, pAtY (P (pureIdxA j)) z
        * (BU a b c HU HL (pureIdxA j) z - BU a b c HU HL (pureIdxA j) (wC z)))
      = ∑ j : Fin 7, pAtY (P (pureIdxA j)) z * (BUp j z - BUp j (wC z)) :=
    Finset.sum_congr rfl (fun j _ => by rw [BU_pureIdxA])
  rw [hG, hI, hP] at hsum
  rw [← hPJ z hzw] at hsum
  exact hsum

private lemma lcA_one_not_mem_ball_ninth {δ : ℝ} (hδ20 : δ ≤ 1 / 20) :
    (1 : ℂ) ∉ Metric.ball ninth δ := by
  intro hmem
  have h := hmem
  rw [Metric.mem_ball, Complex.dist_eq] at h
  have hle : ‖(1 : ℂ) - ninth‖ = 8 / 9 := by norm_num [ninth]
  rw [hle] at h
  linarith

private lemma lcA_two_not_mem_ball_ninth {δ : ℝ} (hδ20 : δ ≤ 1 / 20) :
    (2 : ℂ) ∉ Metric.ball ninth δ := by
  intro hmem
  have h := hmem
  rw [Metric.mem_ball, Complex.dist_eq] at h
  have hle : ‖(2 : ℂ) - ninth‖ = 17 / 9 := by norm_num [ninth]
  rw [hle] at h
  linarith

private lemma lcA_two_not_mem_ball_neg_eighth :
    (2 : ℂ) ∉ Metric.ball (-(1 / 8) : ℂ) (1 / 10) := by
  intro hmem
  have h := hmem
  rw [Metric.mem_ball, Complex.dist_eq] at h
  have hle : ‖(2 : ℂ) - (-(1 / 8))‖ = 17 / 8 := by norm_num
  rw [hle] at h
  linarith

/-- The lower part of the ball of radius `1/10` around `−1/8`. -/
private def lcA_lball : Set ℂ := Metric.ball (-(1 / 8) : ℂ) (1 / 10) ∩ {z : ℂ | z.im < 0}

private lemma lcA_isOpen_lball : IsOpen lcA_lball :=
  Metric.isOpen_ball.inter (isOpen_lt Complex.continuous_im continuous_const)

private lemma lcA_convex_lball : Convex ℝ lcA_lball :=
  (convex_ball _ _).inter (convex_halfSpace_im_lt 0)

private lemma lcA_lball_subset_Om1 : lcA_lball ⊆ Om1 := fun z hz => Or.inl (ne_of_lt hz.2)

private lemma lcA_lball_pt :
    (-(1 / 8) : ℂ) - (((1 / 20 : ℝ)) : ℂ) * Complex.I ∈ lcA_lball := by
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, Complex.dist_eq]
    have h : -(1 / 8 : ℂ) - (((1 / 20 : ℝ)) : ℂ) * Complex.I - (-(1 / 8))
        = -((((1 / 20 : ℝ)) : ℂ) * Complex.I) := by ring
    rw [h, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 20)]
    norm_num
  · show ((-(1 / 8) : ℂ) - (((1 / 20 : ℝ)) : ℂ) * Complex.I).im < 0
    simp [Complex.sub_im, Complex.mul_im, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]

private lemma lcA_wC_mem_lball {δ : ℝ} (hδ20 : δ ≤ 1 / 20) {z : ℂ} (hz : z ∈ halfU δ) :
    wC z ∈ lcA_lball :=
  ⟨wC_maps_ball hδ20 hz.1, wC_im_neg hz.2⟩

private lemma lcA_halfU_open (δ : ℝ) : IsOpen (halfU δ) :=
  Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

private lemma lcA_halfU_convex (δ : ℝ) : Convex ℝ (halfU δ) :=
  (convex_ball _ _).inter (convex_halfSpace_im_gt 0)

private lemma lcA_halfU_subset_bigball {δ : ℝ} (hδ20 : δ ≤ 1 / 20) {z : ℂ}
    (hz : z ∈ halfU δ) : z ∈ Metric.ball ninth (1 / 10) :=
  Metric.ball_subset_ball (by linarith) hz.1

private lemma lcA_halfU_pt {δ : ℝ} (hδ : 0 < δ) :
    ninth + (((δ / 2 : ℝ)) : ℂ) * Complex.I ∈ halfU δ := by
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, Complex.dist_eq]
    have h : ninth + (((δ / 2 : ℝ)) : ℂ) * Complex.I - ninth
        = (((δ / 2 : ℝ)) : ℂ) * Complex.I := by ring
    rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ2]
    linarith
  · show 0 < (ninth + (((δ / 2 : ℝ)) : ℂ) * Complex.I).im
    have him : (ninth + (((δ / 2 : ℝ)) : ℂ) * Complex.I).im = δ / 2 := by
      have hn : ninth = (((1 / 9 : ℝ)) : ℂ) := by rw [ninth]; norm_num
      rw [hn, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_im, Complex.I_re]
      ring
    rw [him]; linarith

/-! ## The identity-theorem steps and the `log`-decomposition of `TJU` and `TJL` -/

/-- On the union of the punctured half plane `SU ∖ {2}` and the upper half plane, `TJU` is
analytic and vanishes near `cWedge`, hence on the upper half disc. -/
private lemma TJU_zero_halfU {a b c : ℤ} {HU HL D PJ : ℂ → ℂ} {P : Fin 14 → Polynomial ℚ}
    {δ : ℝ} (hD : DifferentiableOn ℂ D Om1) (hPJ : DifferentiableOn ℂ PJ Om1)
    (hvan : ∀ z ∈ (SU ∩ SL) \ ({2} : Set ℂ), TJU a b c HU HL D PJ P z = 0) :
    ∀ z ∈ halfU δ, TJU a b c HU HL D PJ P z = 0 := by
  have hopen : IsOpen ((SU \ ({2} : Set ℂ)) ∪ UHalf) :=
    (isOpen_SU_H_cont.sdiff isClosed_singleton).union isOpen_UHalf
  have hana : AnalyticOnNhd ℂ (TJU a b c HU HL D PJ P) ((SU \ ({2} : Set ℂ)) ∪ UHalf) :=
    (TJU_analytic hD hPJ).analyticOnNhd hopen
  have hbase : cWedge ∈ (SU \ ({2} : Set ℂ)) ∪ UHalf :=
    Or.inl ⟨cWedge_mem_wedge.1.1, cWedge_mem_wedge.2⟩
  have hwopen : IsOpen ((SU ∩ SL) \ ({2} : Set ℂ)) :=
    (isOpen_SU_H_cont.inter isOpen_SL_H_cont).sdiff isClosed_singleton
  have hev : (TJU a b c HU HL D PJ P) =ᶠ[𝓝 cWedge] 0 := by
    filter_upwards [hwopen.mem_nhds cWedge_mem_wedge] with w hw
    exact hvan w hw
  have hzero := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    preconnected_SU_union_UHalf hbase hev
  intro z hz
  exact hzero (Or.inr hz.2)

/-- The `SL`-mirror of `TJU_zero_halfU`. -/
private lemma TJL_zero_halfL {a b c : ℤ} {HU HL D PJ : ℂ → ℂ} {P : Fin 14 → Polynomial ℚ}
    {δ : ℝ} (hD : DifferentiableOn ℂ D Om1) (hPJ : DifferentiableOn ℂ PJ Om1)
    (hvan : ∀ z ∈ (SU ∩ SL) \ ({2} : Set ℂ), TJL a b c HU HL D PJ P z = 0) :
    ∀ z ∈ halfL δ, TJL a b c HU HL D PJ P z = 0 := by
  have hopen : IsOpen ((SL \ ({2} : Set ℂ)) ∪ LHalf) :=
    (isOpen_SL_H_cont.sdiff isClosed_singleton).union isOpen_LHalf
  have hana : AnalyticOnNhd ℂ (TJL a b c HU HL D PJ P) ((SL \ ({2} : Set ℂ)) ∪ LHalf) :=
    (TJL_analytic hD hPJ).analyticOnNhd hopen
  have hbase : cWedge ∈ (SL \ ({2} : Set ℂ)) ∪ LHalf :=
    Or.inl ⟨cWedge_mem_wedge.1.2, cWedge_mem_wedge.2⟩
  have hwopen : IsOpen ((SU ∩ SL) \ ({2} : Set ℂ)) :=
    (isOpen_SU_H_cont.inter isOpen_SL_H_cont).sdiff isClosed_singleton
  have hev : (TJL a b c HU HL D PJ P) =ᶠ[𝓝 cWedge] 0 := by
    filter_upwards [hwopen.mem_nhds cWedge_mem_wedge] with w hw
    exact hvan w hw
  have hzero := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    preconnected_SL_union_LHalf hbase hev
  intro z hz
  exact hzero (Or.inr hz.2)

/-- Factoring a `log`-coefficient out of a finite sum. -/
private lemma decomp_alg {ι : Type*} [Fintype ι] (κU L : ℂ) (p D B : ι → ℂ) :
    (∑ k, p k * (κU * D k * L + B k)) = κU * (∑ k, p k * D k) * L + (∑ k, p k * B k) := by
  have h1 : (∑ k, p k * (κU * D k * L + B k))
      = (∑ k, p k * (κU * D k * L)) + (∑ k, p k * B k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have h2 : (∑ k, p k * (κU * D k * L)) = κU * (∑ k, p k * D k) * L := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [h1, h2]

/-- The `log`-decomposition of `TJU` on the upper half disc: the coefficient of `log (z − 1/9)` is
`κU · Xfun` and the remainder has at most a pole at `1/9`. -/
private lemma TJU_decomp {a b c : ℤ} {HU HL D PJ PB De : ℂ → ℂ} {P : Fin 14 → Polynomial ℚ}
    {y9 : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) (κU : ℂ)
    (hY : Y9 y9 δ) (hU : LogCoeff y9 δ (halfU δ) D κU)
    (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDe : DifferentiableOn ℂ De (Metric.ball ninth δ))
    (hDeeq : ∀ z ∈ halfU δ, De z = D (wC z))
    (mP : ℕ) (hPBd : DifferentiableOn ℂ (fun z => (z - ninth) ^ mP * PB z) (Metric.ball ninth δ))
    (hPBeq : ∀ z ∈ halfU δ, PB z = PJ z) :
    ∃ (m : ℕ) (B : ℂ → ℂ),
      DifferentiableOn ℂ (fun z => (z - ninth) ^ m * B z) (Metric.ball ninth δ) ∧
      ∀ z ∈ halfU δ,
        TJU a b c HU HL D PJ P z
          = κU * Xfun P y9 (fun i : Fin 3 => jPrim y9 (i : ℕ)) z * Complex.log (z - ninth)
            + B z := by
  classical
  have hG := fun k : Fin 4 => decomp_G hδ hδ20 κU hY hU hDe hDeeq k
  choose mG BG hBG using hG
  have hI := fun i : Fin 3 => decomp_I hδ hδ20 κU hY hU hD hDL hDe hDeeq i
  choose mI BI hBI using hI
  set Cc : Fin 3 → ℂ := fun i => (BUi a b c HU HL i cWedge - BUi a b c HU HL i (wC cWedge))
    - JFI D i cWedge with hCc
  set m : ℕ := (∑ k : Fin 4, mG k) + (∑ i : Fin 3, mI i) + mP with hm
  set B : ℂ → ℂ := fun z => (∑ k : Fin 4, pAtY (P (gIdxA k)) z * BG k z)
    + (∑ i : Fin 3, pAtY (P (iIdxA i)) z * (BI i z + Cc i)) + PB z with hB
  have hleG : ∀ k : Fin 4, mG k ≤ m := by
    intro k
    have h1 : mG k ≤ ∑ k : Fin 4, mG k :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ k)
    rw [hm]; omega
  have hleI : ∀ i : Fin 3, mI i ≤ m := by
    intro i
    have h1 : mI i ≤ ∑ i : Fin 3, mI i :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hm]; omega
  have hleP : mP ≤ m := by rw [hm]; omega
  refine ⟨m, B, ?_, ?_⟩
  · have hGd : DifferentiableOn ℂ (fun z => (z - ninth) ^ m *
        (∑ k : Fin 4, pAtY (P (gIdxA k)) z * BG k z)) (Metric.ball ninth δ) := by
      rw [show (fun z => (z - ninth) ^ m * (∑ k : Fin 4, pAtY (P (gIdxA k)) z * BG k z))
          = fun z => ∑ k : Fin 4, (z - ninth) ^ m * (pAtY (P (gIdxA k)) z * BG k z) from by
        funext z; rw [Finset.mul_sum]]
      refine DifferentiableOn.fun_sum fun k _ => ?_
      rw [show (fun z => (z - ninth) ^ m * (pAtY (P (gIdxA k)) z * BG k z))
          = fun z => ((z - ninth) ^ (m - mG k)) * ((z - ninth) ^ (mG k) * BG k z)
              * pAtY (P (gIdxA k)) z from by
        funext z
        have hp : (z - ninth) ^ m = (z - ninth) ^ (m - mG k) * (z - ninth) ^ (mG k) := by
          rw [← pow_add, Nat.sub_add_cancel (hleG k)]
        rw [hp]; ring]
      exact (((differentiableOn_id.sub (differentiableOn_const ninth)).pow (m - mG k)).mul
        ((hBG k).1)).mul (pAtY_diffOn (P (gIdxA k)) (fun h1 => lcA_one_not_mem_ball_ninth hδ20 h1))
    have hId : DifferentiableOn ℂ (fun z => (z - ninth) ^ m *
        (∑ i : Fin 3, pAtY (P (iIdxA i)) z * (BI i z + Cc i))) (Metric.ball ninth δ) := by
      rw [show (fun z => (z - ninth) ^ m * (∑ i : Fin 3, pAtY (P (iIdxA i)) z * (BI i z + Cc i)))
          = fun z => ∑ i : Fin 3, (((z - ninth) ^ (m - mI i) * ((z - ninth) ^ (mI i) * BI i z)) * pAtY (P (iIdxA i)) z + ((z - ninth) ^ (m - mI i) * ((z - ninth) ^ (mI i) * (pAtY (P (iIdxA i)) z * Cc i)))) from by
        funext z
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hp : (z - ninth) ^ m = (z - ninth) ^ (m - mI i) * (z - ninth) ^ (mI i) := by
          rw [← pow_add, Nat.sub_add_cancel (hleI i)]
        rw [hp]; ring]
      refine DifferentiableOn.fun_sum fun i _ => ?_
      refine DifferentiableOn.add ?_ ?_
      · have h1 : DifferentiableOn ℂ (fun z => (z - ninth) ^ (m - mI i)
            * ((z - ninth) ^ (mI i) * BI i z)) (Metric.ball ninth δ) :=
          ((differentiableOn_id.sub (differentiableOn_const ninth)).pow (m - mI i)).mul ((hBI i).1)
        exact h1.mul (pAtY_diffOn (P (iIdxA i)) (fun h1 => lcA_one_not_mem_ball_ninth hδ20 h1))
      · have h1 : DifferentiableOn ℂ (fun z => (z - ninth) ^ (m - mI i)
            * ((z - ninth) ^ (mI i) * (pAtY (P (iIdxA i)) z * Cc i))) (Metric.ball ninth δ) :=
          ((differentiableOn_id.sub (differentiableOn_const ninth)).pow (m - mI i)).mul
            (((differentiableOn_id.sub (differentiableOn_const ninth)).pow (mI i)).mul
              ((pAtY_diffOn (P (iIdxA i)) (fun h1 => lcA_one_not_mem_ball_ninth hδ20 h1)).mul
                (differentiableOn_const (Cc i))))
        exact h1
    have hPd : DifferentiableOn ℂ (fun z => (z - ninth) ^ m * PB z) (Metric.ball ninth δ) := by
      rw [show (fun z => (z - ninth) ^ m * PB z)
          = fun z => ((z - ninth) ^ (m - mP)) * ((z - ninth) ^ mP * PB z) from by
        funext z
        have hp : (z - ninth) ^ m = (z - ninth) ^ (m - mP) * (z - ninth) ^ mP := by
          rw [← pow_add, Nat.sub_add_cancel hleP]
        rw [hp]; ring]
      exact ((differentiableOn_id.sub (differentiableOn_const ninth)).pow (m - mP)).mul hPBd
    rw [hB]
    rw [show (fun z => (z - ninth) ^ m * ((∑ k : Fin 4, pAtY (P (gIdxA k)) z * BG k z)
          + (∑ i : Fin 3, pAtY (P (iIdxA i)) z * (BI i z + Cc i)) + PB z))
        = fun z => (z - ninth) ^ m * (∑ k : Fin 4, pAtY (P (gIdxA k)) z * BG k z)
          + (z - ninth) ^ m * (∑ i : Fin 3, pAtY (P (iIdxA i)) z * (BI i z + Cc i))
          + (z - ninth) ^ m * PB z from by
      funext z; ring]
    exact (hGd.add hId).add hPd
  · intro z hz
    have hk : ∀ k : Fin 4, JFG D (k : ℕ) z
        = κU * DyIter (k : ℕ) y9 z * Complex.log (z - ninth) + BG k z :=
      fun k => by simpa only [JFG] using (hBG k).2 z hz
    have hi : ∀ i : Fin 3, JFIc a b c HU HL D i z
        = κU * jPrim y9 (i : ℕ) z * Complex.log (z - ninth) + (BI i z + Cc i) := by
      intro i
      have h1 : JFIc a b c HU HL D i z = Cc i + JFI D i z := rfl
      rw [h1, (hBI i).2 z hz]
      ring
    have hGfac : (∑ k : Fin 4, pAtY (P (gIdxA k)) z * JFG D (k : ℕ) z)
        = κU * (∑ k : Fin 4, pAtY (P (gIdxA k)) z * DyIter (k : ℕ) y9 z)
            * Complex.log (z - ninth) + (∑ k : Fin 4, pAtY (P (gIdxA k)) z * BG k z) := by
      simp only [hk]
      exact decomp_alg κU (Complex.log (z - ninth)) (fun k => pAtY (P (gIdxA k)) z)
        (fun k => DyIter (k : ℕ) y9 z) (fun k => BG k z)
    have hIfac : (∑ i : Fin 3, pAtY (P (iIdxA i)) z * JFIc a b c HU HL D i z)
        = κU * (∑ i : Fin 3, pAtY (P (iIdxA i)) z * jPrim y9 (i : ℕ) z)
            * Complex.log (z - ninth) + (∑ i : Fin 3, pAtY (P (iIdxA i)) z * (BI i z + Cc i)) := by
      simp only [hi]
      exact decomp_alg κU (Complex.log (z - ninth)) (fun i => pAtY (P (iIdxA i)) z)
        (fun i => jPrim y9 (i : ℕ) z) (fun i => BI i z + Cc i)
    rw [show TJU a b c HU HL D PJ P z = (∑ k : Fin 4, pAtY (P (gIdxA k)) z * JFG D (k : ℕ) z)
        + (∑ i : Fin 3, pAtY (P (iIdxA i)) z * JFIc a b c HU HL D i z) + PJ z from rfl,
      ← hPBeq z hz, hGfac, hIfac, hB]
    simp only [Xfun, gIdx, gIdxA, iIdx, iIdxA]
    ring

/-- The `SL`-mirror of `TJU_decomp`. -/
private lemma TJL_decomp {a b c : ℤ} {HU HL D PJ PB De : ℂ → ℂ} {P : Fin 14 → Polynomial ℚ}
    {y9 : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) (κL : ℂ)
    (hY : Y9 y9 δ) (hL : LogCoeff y9 δ (halfL δ) D κL)
    (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDe : DifferentiableOn ℂ De (Metric.ball ninth δ))
    (hDeeq : ∀ z ∈ halfL δ, De z = D (wC z))
    (mP : ℕ) (hPBd : DifferentiableOn ℂ (fun z => (z - ninth) ^ mP * PB z) (Metric.ball ninth δ))
    (hPBeq : ∀ z ∈ halfL δ, PB z = PJ z) :
    ∃ (m : ℕ) (B : ℂ → ℂ),
      DifferentiableOn ℂ (fun z => (z - ninth) ^ m * B z) (Metric.ball ninth δ) ∧
      ∀ z ∈ halfL δ,
        TJL a b c HU HL D PJ P z
          = κL * Xfun P y9 (fun i : Fin 3 => jPrim y9 (i : ℕ)) z * Complex.log (z - ninth)
            + B z := by
  classical
  have hG := fun k : Fin 4 => decomp_G_L hδ hδ20 κL hY hL hDe hDeeq k
  choose mG BG hBG using hG
  have hI := fun i : Fin 3 => decomp_I_L hδ hδ20 κL hY hL hD hDL hDe hDeeq i
  choose mI BI hBI using hI
  set Cc : Fin 3 → ℂ := fun i => (BUi a b c HU HL i cWedge - BUi a b c HU HL i (wC cWedge))
    - primSeg (jIntJ D (i : ℕ)) cSL cWedge with hCc
  set m : ℕ := (∑ k : Fin 4, mG k) + (∑ i : Fin 3, mI i) + mP with hm
  set B : ℂ → ℂ := fun z => (∑ k : Fin 4, pAtY (P (gIdxA k)) z * BG k z)
    + (∑ i : Fin 3, pAtY (P (iIdxA i)) z * (BI i z + Cc i)) + PB z with hB
  have hleG : ∀ k : Fin 4, mG k ≤ m := by
    intro k
    have h1 : mG k ≤ ∑ k : Fin 4, mG k :=
      Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ k)
    rw [hm]; omega
  have hleI : ∀ i : Fin 3, mI i ≤ m := by
    intro i
    have h1 : mI i ≤ ∑ i : Fin 3, mI i :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hm]; omega
  have hleP : mP ≤ m := by rw [hm]; omega
  refine ⟨m, B, ?_, ?_⟩
  · have hGd : DifferentiableOn ℂ (fun z => (z - ninth) ^ m *
        (∑ k : Fin 4, pAtY (P (gIdxA k)) z * BG k z)) (Metric.ball ninth δ) := by
      rw [show (fun z => (z - ninth) ^ m * (∑ k : Fin 4, pAtY (P (gIdxA k)) z * BG k z))
          = fun z => ∑ k : Fin 4, (z - ninth) ^ m * (pAtY (P (gIdxA k)) z * BG k z) from by
        funext z; rw [Finset.mul_sum]]
      refine DifferentiableOn.fun_sum fun k _ => ?_
      rw [show (fun z => (z - ninth) ^ m * (pAtY (P (gIdxA k)) z * BG k z))
          = fun z => ((z - ninth) ^ (m - mG k)) * ((z - ninth) ^ (mG k) * BG k z)
              * pAtY (P (gIdxA k)) z from by
        funext z
        have hp : (z - ninth) ^ m = (z - ninth) ^ (m - mG k) * (z - ninth) ^ (mG k) := by
          rw [← pow_add, Nat.sub_add_cancel (hleG k)]
        rw [hp]; ring]
      exact (((differentiableOn_id.sub (differentiableOn_const ninth)).pow (m - mG k)).mul
        ((hBG k).1)).mul (pAtY_diffOn (P (gIdxA k)) (fun h1 => lcA_one_not_mem_ball_ninth hδ20 h1))
    have hId : DifferentiableOn ℂ (fun z => (z - ninth) ^ m *
        (∑ i : Fin 3, pAtY (P (iIdxA i)) z * (BI i z + Cc i))) (Metric.ball ninth δ) := by
      rw [show (fun z => (z - ninth) ^ m * (∑ i : Fin 3, pAtY (P (iIdxA i)) z * (BI i z + Cc i)))
          = fun z => ∑ i : Fin 3, (((z - ninth) ^ (m - mI i) * ((z - ninth) ^ (mI i) * BI i z)) * pAtY (P (iIdxA i)) z + ((z - ninth) ^ (m - mI i) * ((z - ninth) ^ (mI i) * (pAtY (P (iIdxA i)) z * Cc i)))) from by
        funext z
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hp : (z - ninth) ^ m = (z - ninth) ^ (m - mI i) * (z - ninth) ^ (mI i) := by
          rw [← pow_add, Nat.sub_add_cancel (hleI i)]
        rw [hp]; ring]
      refine DifferentiableOn.fun_sum fun i _ => ?_
      refine DifferentiableOn.add ?_ ?_
      · have h1 : DifferentiableOn ℂ (fun z => (z - ninth) ^ (m - mI i)
            * ((z - ninth) ^ (mI i) * BI i z)) (Metric.ball ninth δ) :=
          ((differentiableOn_id.sub (differentiableOn_const ninth)).pow (m - mI i)).mul ((hBI i).1)
        exact h1.mul (pAtY_diffOn (P (iIdxA i)) (fun h1 => lcA_one_not_mem_ball_ninth hδ20 h1))
      · have h1 : DifferentiableOn ℂ (fun z => (z - ninth) ^ (m - mI i)
            * ((z - ninth) ^ (mI i) * (pAtY (P (iIdxA i)) z * Cc i))) (Metric.ball ninth δ) :=
          ((differentiableOn_id.sub (differentiableOn_const ninth)).pow (m - mI i)).mul
            (((differentiableOn_id.sub (differentiableOn_const ninth)).pow (mI i)).mul
              ((pAtY_diffOn (P (iIdxA i)) (fun h1 => lcA_one_not_mem_ball_ninth hδ20 h1)).mul
                (differentiableOn_const (Cc i))))
        exact h1
    have hPd : DifferentiableOn ℂ (fun z => (z - ninth) ^ m * PB z) (Metric.ball ninth δ) := by
      rw [show (fun z => (z - ninth) ^ m * PB z)
          = fun z => ((z - ninth) ^ (m - mP)) * ((z - ninth) ^ mP * PB z) from by
        funext z
        have hp : (z - ninth) ^ m = (z - ninth) ^ (m - mP) * (z - ninth) ^ mP := by
          rw [← pow_add, Nat.sub_add_cancel hleP]
        rw [hp]; ring]
      exact ((differentiableOn_id.sub (differentiableOn_const ninth)).pow (m - mP)).mul hPBd
    rw [hB]
    rw [show (fun z => (z - ninth) ^ m * ((∑ k : Fin 4, pAtY (P (gIdxA k)) z * BG k z)
          + (∑ i : Fin 3, pAtY (P (iIdxA i)) z * (BI i z + Cc i)) + PB z))
        = fun z => (z - ninth) ^ m * (∑ k : Fin 4, pAtY (P (gIdxA k)) z * BG k z)
          + (z - ninth) ^ m * (∑ i : Fin 3, pAtY (P (iIdxA i)) z * (BI i z + Cc i))
          + (z - ninth) ^ m * PB z from by
      funext z; ring]
    exact (hGd.add hId).add hPd
  · intro z hz
    have hk : ∀ k : Fin 4, JFG D (k : ℕ) z
        = κL * DyIter (k : ℕ) y9 z * Complex.log (z - ninth) + BG k z :=
      fun k => by simpa only [JFG] using (hBG k).2 z hz
    have hi : ∀ i : Fin 3, JFIc_L a b c HU HL D i z
        = κL * jPrim y9 (i : ℕ) z * Complex.log (z - ninth) + (BI i z + Cc i) := by
      intro i
      have h1 : JFIc_L a b c HU HL D i z = Cc i + JFI_L D i z := rfl
      have h2 : JFI_L D i z
          = primSeg (fun ζ => dyC ζ * (yC ζ)⁻¹ ^ (i : ℕ) * jumpH D ζ) cSL z := rfl
      rw [h1, h2, (hBI i).2 z hz]
      ring
    have hGfac : (∑ k : Fin 4, pAtY (P (gIdxA k)) z * JFG D (k : ℕ) z)
        = κL * (∑ k : Fin 4, pAtY (P (gIdxA k)) z * DyIter (k : ℕ) y9 z)
            * Complex.log (z - ninth) + (∑ k : Fin 4, pAtY (P (gIdxA k)) z * BG k z) := by
      simp only [hk]
      exact decomp_alg κL (Complex.log (z - ninth)) (fun k => pAtY (P (gIdxA k)) z)
        (fun k => DyIter (k : ℕ) y9 z) (fun k => BG k z)
    have hIfac : (∑ i : Fin 3, pAtY (P (iIdxA i)) z * JFIc_L a b c HU HL D i z)
        = κL * (∑ i : Fin 3, pAtY (P (iIdxA i)) z * jPrim y9 (i : ℕ) z)
            * Complex.log (z - ninth) + (∑ i : Fin 3, pAtY (P (iIdxA i)) z * (BI i z + Cc i)) := by
      simp only [hi]
      exact decomp_alg κL (Complex.log (z - ninth)) (fun i => pAtY (P (iIdxA i)) z)
        (fun i => jPrim y9 (i : ℕ) z) (fun i => BI i z + Cc i)
    rw [show TJL a b c HU HL D PJ P z = (∑ k : Fin 4, pAtY (P (gIdxA k)) z * JFG D (k : ℕ) z)
        + (∑ i : Fin 3, pAtY (P (iIdxA i)) z * JFIc_L a b c HU HL D i z) + PJ z from rfl,
      ← hPBeq z hz, hGfac, hIfac, hB]
    simp only [Xfun, gIdx, gIdxA, iIdx, iIdxA]
    ring

/-! ## The upper-half-disc germ of the pure part, and the final assembly helpers -/

/-- The pure part of the jump relation, with the germ at `1/9` taken from the *upper* half disc
(`Work.A14D.pure_part_lower` gives the lower one). -/
private lemma asm_pure_part_upper (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c)
    (P : Fin 14 → Polynomial ℚ) {δ : ℝ} (hδ : 0 < δ) (hδ20 : δ ≤ 1 / 20) :
    ∃ (PJ : ℂ → ℂ) (PB : ℂ → ℂ) (m : ℕ),
      DifferentiableOn ℂ PJ Om1 ∧
      (∀ z ∈ SU ∩ SL, PJ z
        = ∑ j : Fin 7, pAtY (P (pureIdxA j)) z * (BUp j z - BUp j (wC z))) ∧
      DifferentiableOn ℂ (fun z => (z - ninth) ^ m * PB z) (Metric.ball ninth δ) ∧
      (∀ z ∈ halfU δ, PB z = PJ z) := by
  obtain ⟨G, hGd, hGSU, hGode⟩ := exists_G_Om1
  -- the ODEs of `G` on the two half discs, in the form expected by `exists_sol_of_sol_convex`
  have hfun0 : ∀ z : ℂ, (fun i : Fin 7 => ∑ j : Fin 7, psysA z i j * G z j
      + (fun _ : ℂ => (0 : Fin 7 → ℂ)) z i) = fun i : Fin 7 => ∑ j : Fin 7, psysA z i j * G z j :=
    fun z => by funext i; simp
  have hodeU : ∀ z ∈ halfU δ, HasDerivAt G (fun i => ∑ j : Fin 7, psysA z i j * G z j
      + (fun _ : ℂ => (0 : Fin 7 → ℂ)) z i) z := by
    intro z hz
    rw [hfun0 z]
    exact hGode z (Or.inl (ne_of_gt hz.2))
      (fun h2 => lcA_two_not_mem_ball_ninth (δ := 1 / 20) le_rfl
        (Metric.ball_subset_ball hδ20 (h2 ▸ hz.1)))
  have hodeL : ∀ z ∈ lcA_lball, HasDerivAt G (fun i => ∑ j : Fin 7, psysA z i j * G z j
      + (fun _ : ℂ => (0 : Fin 7 → ℂ)) z i) z := by
    intro z hz
    rw [hfun0 z]
    exact hGode z (lcA_lball_subset_Om1 hz) (fun h2 => lcA_two_not_mem_ball_neg_eighth (h2 ▸ hz.1))
  -- the extension of `G` from the upper half disc to a disc around `1/9`
  obtain ⟨F, hFd, hFeq⟩ := exists_sol_of_sol_convex (b := fun _ : ℂ => (0 : Fin 7 → ℂ))
    (lcA_halfU_convex δ) (lcA_halfU_open δ)
    (convex_ball _ _) Metric.isOpen_ball (fun z hz => lcA_halfU_subset_bigball hδ20 hz)
    (fun i j => psysA_diffOn_ball i j)
    (fun i => differentiableOn_const 0)
    (hGd.mono (fun z hz => Or.inl (ne_of_gt hz.2))) hodeU (lcA_halfU_pt hδ)
  -- the extension of `G` from a lower disc around `−1/8`
  obtain ⟨H, hHd, hHeq⟩ := exists_sol_of_sol_convex (b := fun _ : ℂ => (0 : Fin 7 → ℂ))
    (lcA_convex_lball) lcA_isOpen_lball
    (convex_ball _ _) Metric.isOpen_ball (fun z hz => hz.1)
    (fun i j => psysA_diffOn_ball_neg i j)
    (fun i => differentiableOn_const 0)
    (hGd.mono (fun z hz => lcA_lball_subset_Om1 hz)) hodeL lcA_lball_pt
  refine ⟨PJfun P G, fun z => ∑ j : Fin 7, pAtY (P (pureIdxA j)) z * (F z j - H (wC z) j), 0,
    PJfun_diffOn P G hGd, fun z hz => PJfun_wedge P G hGSU hz, ?_, ?_⟩
  · have h1 : ∀ j : Fin 7, DifferentiableOn ℂ (fun z => F z j) (Metric.ball ninth δ) := fun j =>
      (differentiableOn_pi.mp hFd j).mono (fun z hz => Metric.ball_subset_ball (by linarith) hz)
    have h2 : ∀ j : Fin 7, DifferentiableOn ℂ (fun z => H (wC z) j) (Metric.ball ninth δ) := by
      intro j
      have hHj : DifferentiableOn ℂ (fun z => H z j) (Metric.ball (-(1 / 8) : ℂ) (1 / 10)) :=
        differentiableOn_pi.mp hHd j
      have hw : DifferentiableOn ℂ wC (Metric.ball ninth δ) :=
        wC_diffOn_of_notMem_one (fun h1 => lcA_one_not_mem_ball_ninth hδ20 h1)
      exact hHj.comp hw (fun z hz => wC_maps_ball hδ20 hz)
    have hmain : DifferentiableOn ℂ (fun z => ∑ j : Fin 7,
        pAtY (P (pureIdxA j)) z * (F z j - H (wC z) j)) (Metric.ball ninth δ) :=
      DifferentiableOn.fun_sum fun j _ =>
        (pAtY_diffOn (P (pureIdxA j)) (fun h1 => lcA_one_not_mem_ball_ninth hδ20 h1)).mul
          ((h1 j).sub (h2 j))
    simpa using hmain
  · intro z hz
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hFeq hz, hHeq (lcA_wC_mem_lball hδ20 hz)]

/-- The `(LC)` expression of the target in the shape produced by the decomposition. -/
private lemma asm_Xfun_eq (P : Fin 14 → Polynomial ℚ) (y9 : ℂ → ℂ) (J : Fin 3 → ℂ → ℂ)
    (z : ℂ) :
    Xfun P y9 J z
      = (∑ k : Fin 4, pAtY (P ⟨5 + (k : ℕ), by omega⟩) z * DyIter k y9 z)
        + (∑ i : Fin 3, pAtY (P ⟨11 + (i : ℕ), by omega⟩) z * J i z) := by
  simp only [Xfun, gIdx, gIdxA, iIdx, iIdxA]

/-- `Xfun`, with the canonical primitives `jPrim y9 i`, is holomorphic on the disc. -/
private lemma Xfun_jPrim_diffOn {y9 : ℂ → ℂ} {δ : ℝ} (hY : Y9 y9 δ)
    (P : Fin 14 → Polynomial ℚ) :
    DifferentiableOn ℂ (Xfun P y9 (fun i : Fin 3 => jPrim y9 (i : ℕ))) (Metric.ball ninth δ) := by
  have hδ20 : δ ≤ 1 / 20 := hY.2.1
  have hy9d : DifferentiableOn ℂ y9 (Metric.ball ninth δ) := hY.2.2.1
  have h1 : DifferentiableOn ℂ
      (fun z => ∑ k : Fin 4, pAtY (P (gIdx k)) z * DyIter (k : ℕ) y9 z)
      (Metric.ball ninth δ) :=
    DifferentiableOn.fun_sum fun k _ =>
      (pAtY_diffOn (P (gIdx k)) (fun h1 => lcA_one_not_mem_ball_ninth hδ20 h1)).mul
        (dyIter_diffOn_ninth hδ20 hy9d (k : ℕ))
  have h2 : DifferentiableOn ℂ
      (fun z => ∑ i : Fin 3, pAtY (P (iIdx i)) z * jPrim y9 (i : ℕ) z)
      (Metric.ball ninth δ) :=
    DifferentiableOn.fun_sum fun i _ =>
      (pAtY_diffOn (P (iIdx i)) (fun h1 => lcA_one_not_mem_ball_ninth hδ20 h1)).mul
        (fun z hz => (jPrim_hasDerivAt hY i z hz).differentiableAt.differentiableWithinAt)
  rw [show Xfun P y9 (fun i : Fin 3 => jPrim y9 (i : ℕ))
      = fun z => (∑ k : Fin 4, pAtY (P (gIdx k)) z * DyIter (k : ℕ) y9 z)
        + (∑ i : Fin 3, pAtY (P (iIdx i)) z * jPrim y9 (i : ℕ) z) from rfl]
  exact h1.add h2

/-- The one-sided extraction on the *lower* half disc (the mirror of `extract_log_half`, via
`half_log_vanishes`). -/
private lemma asm_extract_log_half_L {δ : ℝ} (hδ : 0 < δ) {A B : ℂ → ℂ} (m : ℕ)
    (hA : DifferentiableOn ℂ A (Metric.ball ninth δ))
    (hB : DifferentiableOn ℂ (fun z => (z - ninth) ^ m * B z) (Metric.ball ninth δ))
    (hid : ∀ z ∈ halfL δ, A z * Complex.log (z - ninth) + B z = 0) :
    ∀ z ∈ Metric.ball ninth δ, A z = 0 := by
  set Ah : ℂ → ℂ := fun z => (z - ninth) ^ m * A z with hAh
  set Bh : ℂ → ℂ := fun z => (z - ninth) ^ m * B z with hBh
  have hAhd : DifferentiableOn ℂ Ah (Metric.ball ninth δ) := by
    rw [hAh]
    exact ((differentiableOn_id.sub (differentiableOn_const ninth)).pow m).mul hA
  have hBhd : DifferentiableOn ℂ Bh (Metric.ball ninth δ) := hB
  have hid' : ∀ z ∈ halfL δ, Ah z * Complex.log (z - ninth) = -Bh z := by
    intro z hz
    have h := hid z hz
    have h3 : (z - ninth) ^ m * (A z * Complex.log (z - ninth)) + (z - ninth) ^ m * B z = 0 := by
      have h4 := congrArg (fun x : ℂ => (z - ninth) ^ m * x) h
      simpa only [mul_add, mul_zero] using h4
    rw [hAh, hBh, mul_assoc]
    exact eq_neg_of_add_eq_zero_left h3
  have hzero : ∀ z ∈ Metric.ball ninth δ, Ah z = 0 :=
    half_log_vanishes hδ hAhd hBhd.neg hid'
  have hA0 : ∀ z ∈ Metric.ball ninth δ, z ≠ ninth → A z = 0 := by
    intro z hz hzne
    have h := hzero z hz
    rw [hAh] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero m (sub_ne_zero.mpr hzne))
  intro z hz
  by_cases hzne : z = ninth
  · subst hzne
    have hcont : ContinuousAt A ninth :=
      hA.continuousOn.continuousAt (Metric.ball_mem_nhds ninth hδ)
    have heq0 : (fun z : ℂ => A z) =ᶠ[𝓝[≠] ninth] 0 := by
      rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
      filter_upwards [Metric.ball_mem_nhds ninth hδ] with z hzball hzne'
      exact hA0 z hzball (by simpa using hzne')
    have hlim0 : Filter.Tendsto A (𝓝[≠] ninth) (𝓝 0) :=
      Filter.Tendsto.congr' heq0.symm tendsto_const_nhds
    have hlimA : Filter.Tendsto A (𝓝[≠] ninth) (𝓝 (A ninth)) :=
      hcont.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique hlimA hlim0
  · exact hA0 z hz hzne

theorem relation_to_LC_A (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) (P : Fin 14 → Polynomial ℚ)
    (hrel : ∑ i : Fin 14, (P i : PowerSeries ℚ) * Submission.CDTPlan.fourteen a b c i = 0)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU ∧ (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧
      ∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL SL ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
      ∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z)
    (y9 : ℂ → ℂ) (δ : ℝ) (hY : Y9 y9 δ) (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1)
    (hDL : ∀ z ∈ Om1, LZ D z = 0) (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z)
    (κU κL : ℂ) (hU : LogCoeff y9 δ (halfU δ) D κU) (hL : LogCoeff y9 δ (halfL δ) D κL) :
    ∃ J : Fin 3 → ℂ → ℂ,
      (∀ i, DifferentiableOn ℂ (J i) (ball ninth δ)) ∧ (∀ i, J i ninth = 0) ∧
      (∀ i : Fin 3, ∀ z ∈ ball ninth δ, HasDerivAt (J i) ((yC z)⁻¹ ^ (i : ℕ) * dyC z * y9 z) z) ∧
      ∀ z ∈ ball ninth δ,
        κU * ((∑ k : Fin 4, pAtY (P ⟨5 + k, by omega⟩) z * DyIter k y9 z)
              + ∑ i : Fin 3, pAtY (P ⟨11 + i, by omega⟩) z * J i z) = 0 ∧
        κL * ((∑ k : Fin 4, pAtY (P ⟨5 + k, by omega⟩) z * DyIter k y9 z)
              + ∑ i : Fin 3, pAtY (P ⟨11 + i, by omega⟩) z * J i z) = 0 := by
  have hδpos : (0 : ℝ) < δ := hY.1
  have hδ20 : δ ≤ 1 / 20 := hY.2.1
  obtain ⟨hHUd, hHUlz, hHUeq⟩ := hHU
  obtain ⟨hHLd, hHLlz, hHLeq⟩ := hHL
  refine ⟨fun i : Fin 3 => jPrim y9 (i : ℕ), ?_, ?_, ?_, ?_⟩
  · intro i
    exact fun z hz => (jPrim_hasDerivAt hY i z hz).differentiableAt.differentiableWithinAt
  · intro i
    exact jPrim_ninth y9 i
  · intro i z hz
    exact jPrim_hasDerivAt hY i z hz
  · intro z hz
    obtain ⟨PJ, PB, mP, hPJd, hPJwedge, hPBd, hPBeq⟩ := asm_pure_part_upper a b c h P hδpos hδ20
    obtain ⟨PJL, PBL, mPL, hPJLd, hPJLwedge, hPBLd, hPBLeq⟩ :=
      pure_part_lower a b c h P hδpos hδ20
    constructor
    · -- the `κU` conjunct
      have hwedge := TJU_wedge a b c h P hrel hHUd hHLd hHUeq hHLeq hD hDj hPJwedge
      have hhalf := TJU_zero_halfU (δ := δ) hD hPJd hwedge
      obtain ⟨De, hDed, hDeeq⟩ := Dw_extends hD hDL hδpos hδ20
      obtain ⟨m, B, hBd, hBv⟩ := TJU_decomp (y9 := y9) (δ := δ) hδpos hδ20 κU hY hU hD hDL
        hDed hDeeq mP hPBd hPBeq
      have hA : DifferentiableOn ℂ
          (fun z => κU * Xfun P y9 (fun i : Fin 3 => jPrim y9 (i : ℕ)) z)
          (Metric.ball ninth δ) :=
        (Xfun_jPrim_diffOn hY P).const_mul κU
      have hid : ∀ z ∈ halfU δ,
          (κU * Xfun P y9 (fun i : Fin 3 => jPrim y9 (i : ℕ)) z)
            * Complex.log (z - ninth) + B z = 0 := by
        intro w hw
        rw [← hBv w hw, hhalf w hw]
      have hzero := extract_log_half hδpos m hA hBd hid
      rw [← asm_Xfun_eq P y9 (fun i : Fin 3 => jPrim y9 (i : ℕ)) z]
      exact hzero z hz
    · -- the `κL` conjunct
      have hwedge := TJL_wedge a b c h P hrel hHUd hHLd hHUeq hHLeq hD hDj hPJLwedge
      have hhalf := TJL_zero_halfL (δ := δ) hD hPJLd hwedge
      obtain ⟨De, hDed, hDeeq⟩ := Dw_extends_L hD hDL hδpos hδ20
      obtain ⟨m, B, hBd, hBv⟩ := TJL_decomp (y9 := y9) (δ := δ) hδpos hδ20 κL hY hL hD hDL
        hDed hDeeq mPL hPBLd hPBLeq
      have hA : DifferentiableOn ℂ
          (fun z => κL * Xfun P y9 (fun i : Fin 3 => jPrim y9 (i : ℕ)) z)
          (Metric.ball ninth δ) :=
        (Xfun_jPrim_diffOn hY P).const_mul κL
      have hid : ∀ z ∈ halfL δ,
          (κL * Xfun P y9 (fun i : Fin 3 => jPrim y9 (i : ℕ)) z)
            * Complex.log (z - ninth) + B z = 0 := by
        intro w hw
        rw [← hBv w hw, hhalf w hw]
      have hzero := asm_extract_log_half_L hδpos m hA hBd hid
      rw [← asm_Xfun_eq P y9 (fun i : Fin 3 => jPrim y9 (i : ℕ)) z]
      exact hzero z hz

end Work.A14D
