import Mathlib
import Submission.Work.Mostow.normalForm
import Submission.Work.Mostow.parabolic_not_commute_levelScaling
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.stabFlatAction
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc

/-!
# Route for `Work.Mostow.cuspNoLox` (no declarations here; this file is documentation + imports)

Target (`Submission/Work/Mostow/cuspNoLox.lean`): if `Γ ≤ PO(n,1)` is discrete, `q ∈ Γ` is
parabolic with `bd q ξ = ξ` (`ξ ∈ Sph n`) and `g ∈ Γ` satisfies `bd g ξ = ξ`, then
`busemann ξ (g • 0) = 0`.

Write `β := busemann ξ (g • 0)` (equal to `bCocy g ξ` because `bd g ξ = ξ`) and suppose `β ≠ 0`.

1. **Reduce to `β > 0`.**  Apply the Busemann cocycle (`HypIsoData.busemann_cocycle` of `hI`) to
   `g⁻¹` to get `busemann ξ (g⁻¹ • 0) = -busemann ξ (g • 0)`; `g⁻¹ ∈ Γ` and `bd g⁻¹ ξ = ξ`.  So we
   may assume `β > 0` (replacing `g` by `g⁻¹`, which just flips the sign of the level).

2. **Normal form of `g`.**  `Work.Mostow.normalForm hξ hgξ` gives `b : ℝ`, `A : E n →ₗ[ℝ] E n`,
   `v : E n` with `0 < b`, `v ⊥ ξ`, `A` preserves `ξ^⊥` and is norm preserving there, and for all
   `y ⊥ ξ`, `D > 0`:
   `lev ξ (g • hptOf ξ y D) = b * D` and `yc ξ (g • hptOf ξ y D) = b⁻¹ • (A y) + v`.
   With `y = 0`, `D = 1` (and `hptOf ξ 0 1 = 0`, `lev ξ 0 = 1`, `yc ξ 0 = 0`) this gives
   `b = lev ξ (g • 0) = Real.exp β`, hence `0 < b < 1`.

3. **Normal form of `q`.**  `bCocy q ξ = busemann ξ (q • 0) = 0`
   (`Work.Mostow.bCocy_parabolic`, or `Work.Mostow.pcf_busemann_smul_of_parabolic`), so the same
   normal form applied to `q` has scale `1`: `lev ξ (q • u) = lev ξ u` and
   `yc ξ (q • u) = A_q (yc ξ u) + v_q` for **all** `u` (write `u = hptOf ξ (yc ξ u) (lev ξ u)` with
   `hptOf_yc`, `hptOf_level`, `lev_pos`, `yc_inner_orth`).  Also `‖A_q y‖ = ‖y‖` for `y ⊥ ξ`.

4. **The flat coordinate of the orbit grows at most like `b ^ (-N)`.**  Set `u_N := g ^ N • 0` and
   `y_N := yc ξ u_N`.  Step 2 gives `lev ξ u_N = b ^ N` and `y_{N+1} = b⁻¹ • (A y_N) + v`, `y_0 = 0`.
   By induction using `‖A y‖ = ‖y‖`, `‖y_N‖ ≤ ‖v‖ * ∑_{i<N} b⁻¹^i ≤ C * b ^ (-N)` for a constant
   `C` depending only on `b, v` (any explicit expression works).  Hence
   `‖wc ξ u_N‖ = lev ξ u_N * ‖y_N‖ ≤ C` (`Work.Mostow.wc_eq_lev_smul_yc`).

5. **Uniform bound on the displacement of `q` along that orbit.**
   `Work.Mostow.levYcFormula hξ u_N (q • u_N)` together with `lev ξ (q • u_N) = lev ξ u_N` (step 3)
   gives `Real.cosh (hdist u_N (q • u_N)) = 1 + (lev ξ u_N)^2 * ‖A_q y_N + v_q - y_N‖^2 / 2`; with
   `‖A_q y_N + v_q - y_N‖ ≤ 2 ‖y_N‖ + ‖v_q‖` this is `≤ 1 + (2*C + ‖v_q‖)^2 / 2` uniformly in `N`.
   (The proof of `Work.Mostow.pnc_lev_smul_le_one`, in
   `Mostow/parabolic_not_commute_levelScaling.lean`, contains exactly this computation as `hdisp`.)

6. **Finiteness.**  The elements `q_N := g⁻¹^N * q * g^N = g^{-N} * q * g^N` lie in `Γ` and satisfy
   `hdist 0 (q_N • 0) = hdist u_N (q • u_N)` (push the isometry `g^N`: `isom_smul` of `hI`,
   `mul_smul` of `hA`).  So every `q_N` lies in the finite set `{γ : Γ | hdist 0 (γ • 0) ≤ R}`
   supplied by `Work.Mostow.finite_nearStab (POBasic.ofProp hA) (HypIsoData.ofProp hI) hdisc R`
   for the bound `R` of step 5, and therefore `N ↦ q_N` has finite range: there are `N < M` with
   `q_N = q_M`, i.e. `g ^ (M - N) * q = q * g ^ (M - N)`.

7. **Contradiction.**  Apply
   `Work.Mostow.parabolic_not_commute_levelScaling n hn hA hI q g hq hξ hqξ hgξ hc m hm hcomm`
   with `m := M - N > 0`, `hc : bCocy g ξ ≠ 0` (from `β ≠ 0`, by `bCocy` and `hgξ`) and the
   commutation of step 6.  Alternatively, the commuting case can be finished directly from steps 2
   and 3: commuting the two affine flat actions gives `A_q A = A A_q` and
   `(A_q - 1) v_g = (b⁻¹ A - 1) v_q`; since `b⁻¹ A - 1` is invertible on `ξ^⊥` and preserves
   `range (A_q - 1)`, we get `v_q ∈ range (A_q - 1)`, so `q` fixes the interior point
   `hptOf ξ y 1` for a solution `y`, contradicting `hq.1`.
-/
