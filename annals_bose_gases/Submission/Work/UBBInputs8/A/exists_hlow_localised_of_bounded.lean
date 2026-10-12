import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.UBBInputs8.A.abs_qLHSBIntegrand_le
import Submission.Work.UBBInputs8.A.exists_fibre_wSmall1Pair_le_T
import Submission.Work.UBBInputs8.A.integrableOn_hlowDom
import Submission.Work.UBBInputs8.A.integral_hlowDom_le
import Submission.Work.UBBInputs8.A.sq_integral_chiSmallB_le
import Submission.Work.UBBInputs8.A.tBwordB_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Submission.BoseGases

/-- **The corpus alias of the radiality predicate of a potential.**

`Submission.BoseGases` carries every other object of the potential dictionary
(`chiSmallB`, `wSmallPair`, `abox`, `CSBox`, `chiSmall`, …) but `IsRadial` itself lives only in
`_root_.BoseGases` (`ChallengeDeps.lean`), so the identifier `Submission.BoseGases.IsRadial` did
not exist.  It is supplied here as an abbreviation of `_root_.BoseGases.IsRadial` — the predicate
`IsScatteringSolution` and `Submission.BoseGases.chosen_w0_bounds_ae` consume — so that the
statement of `Work.UBBInputs8.A.exists_hlow_localised_of_bounded` elaborates *verbatim* as
delivered.  Nothing else about the statement is changed. -/
abbrev IsRadial (v : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop := _root_.BoseGases.IsRadial v

end Submission.BoseGases

namespace Work.UBBInputs8.A

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! Round 8, strand A3 — the `hlow` field under the *honest* sufficient hypotheses.

Round 8's prover for `Work.UBBInputs8.A.exists_hlow_localised` (the pointwise per-box bound
`−C·chiMass ≤ tBwordB u Φ + qLHSwordB u Φ` with a `u`-uniform `C`) returned the judgment that the
statement is **false** as it stands: the *pair* kernel of the localised word,
`Work.DLSmallKernels.wSmallPair M ℓ d u v a b
 = χ_{B(u)}(a)·(v(a−b)/(χ_M⋆χ_M)((a−b)/(ℓd)))·χ_{B(u)}(b)`, carries the **raw** potential as its
numerator (only the one-body kernel `wSmall1Pair` uses `g₀ = v(1−w₀)`), and FS's
Assumption (Potentials) (`final_v2.tex` `assump:v`) is only *non-negative, radial, `L¹`, compact
support* — `v` may be unbounded, whereas `Work.UBB.ScatSol v` controls only `g₀`
(`Work.UBB.g0_integrable`).  The repair is to assume exactly what FS's Assumption gives:

    `0 ≤ v`, `IsRadial v`, and `∃ Bv, ∀ y, |v y| ≤ Bv`   (boundedness of the potential)

The radiality and non-negativity are needed for the *one-body* half as well: they give
`0 ≤ w₀ ≤ 1` (`Submission.BoseGases.chosen_w0_bounds_ae`, `w1c_fibre_acube_abs_le`), hence
`|g₀ v h| ≤ |v| ≤ Bv` pointwise.  (FS's own discarded-box mechanism does not need this
boundedness: they drop the non-negative kinetic and repulsion on `Gᶜ` and use the *integrated*
`eq:badset` estimate; see `Work.UBBInputs8.A.sliding_bound_canonical_of_compl_lower` for that
FS-shaped input, which replaces `hlow`.)

Route, with `‖χ_B(u)‖₂² = chiMass M L d u`, `∫χ_B(u) ≤ chiMass^{1/2}·|B(u)|^{1/2}` and
`|B(u)| ≤ (Ld)³` (Cauchy–Schwarz; `Work.SmallBoxSliding.boxMass`):
* `Work.SmallBoxSliding.abs_wSmall1Pair_le` and the analogous two-factor bound for `wSmallPair`
  (with `Work.DLSmallKernels.wSmallScaled`, whose denominator
  `Work.DLSmallKernels.convScaleSmall` is bounded below by `smallConvLower M > 0` **on the support
  of the numerator**: `hv_supp` + `hdR` put `|x − y| ≤ R0 ≤ (Ld)/16`, where `χ_M ⋆ χ_M` does not
  degenerate); the kernels are supported in `χ_B(u) ≠ 0 ⊆ dlBox L d u` (`Work.DLInfra.chiB`);
* hence `|∫_y wSmall1Pair(u,x_i,y)dy| ≤ C₁·χ_B(u)(x_i)·chiMass^{1/2}·(Ld)^{3/2}` (with `C₁` from
  `Bv` and `1/smallConvLower M`) and `|wSmallPair(u,x,y)| ≤ C₂·χ_B(u)(x)·χ_B(u)(y)` with
  `C₂ = Bv/smallConvLower M`;
* `Φ` is continuous on the compact box, hence `sup_{abox} Φ² < ∞`; the `x ∈ abox N L` integrals of
  the `χ_B`-factors give `(∫χ_B)² ≤ chiMass·(Ld)³` per pair;
* collecting, `∫_{abox} Φ²K(u,·) ≥ −C·chiMass` with `C` a product of `sup Φ²`, `N²`, `Bv`,
  `1/smallConvLower M`, `(Ld)³` and the ambient box volume — independent of `u`.  `0 ≤ ε` is
  needed for `tbGapCoeff (Ld) ε ≥ 0` (`Work.SmallBoxTBWord.tbGapCoeff_nonneg`), and `c` is free
  (`Submission.BoseGases.fsKinCoeff_nonneg`).
On the far set and on degenerate (null) boxes `χ_B(u) ≡ 0`, so `K = 0` there and the inequality is
`0 ≤ 0`.

## Prover's record (Session-195)

**(i) The missing identifier.**  As delivered the statement did not elaborate: the identifier
`Submission.BoseGases.IsRadial` did not exist anywhere in the workspace (`IsRadial` lives only in
`_root_.BoseGases`, `ChallengeDeps.lean:80`, while `Submission.BoseGases` carries every *other*
object of the potential dictionary).  The statement itself is therefore kept **verbatim**: what is
supplied is the missing name, as the abbreviation
`Submission.BoseGases.IsRadial := _root_.BoseGases.IsRadial` declared just below the imports —
the predicate that `IsScatteringSolution` and `Submission.BoseGases.chosen_w0_bounds_ae` (the
lemma the estimate actually consumes) use.  No hypothesis, quantifier or conclusion is altered.

**(ii) The route actually formalised** (slightly different from the sketch above, and *linear* in
`chiMass` at every step):

* `Work.UBBInputs8.A.exists_fibre_wSmall1Pair_le_T` — the *pair* half needs no sharpening because
  the two-body kernel carries the two cutoffs: with `χ := χ_{B(u)}`, `T := ∫χ` and
  `Bv := the bound on |v|`, `|∫_{acube L} w_{1,B(u)}(z,y)dy| ≤ (Bv/smallConvLower M)·T·χ(z)`,
  from `|g₀| = |v(1−w₀)| ≤ |v| ≤ Bv` a.e. (`chosen_w0_bounds_ae`, i.e. exactly where `hv`/`hvrad`
  are used) and `abs_wSmallScaled_le`.  `Work.UBBInputs8.A.abs_wSmallPair_chiB_le` gives the
  two-body bound `|w_{B(u)}(x,y)| ≤ (Bv/smallConvLower M)·χ(x)χ(y)`;
* `Work.UBBInputs8.A.abs_qLHSBIntegrand_le` assembles the pointwise domination of
  `qLHSBIntegrand` by `S·(μ·KL·T·Σᵢχ(xᵢ) + ½·KP·Σ_p χ(x_p1)χ(x_p2))` on the box, `S` being a
  bound for `Φ²` (continuity on the compact box);
* `Work.UBBInputs8.A.sq_integral_chiSmallB_le` (Cauchy–Schwarz) gives `T² ≤ chiMass·(Ld)³` — this
  is what makes the one-body half linear in `chiMass`, whereas `T ≤ sup χ·(Ld)³` would only give
  `√chiMass` and is *false* to use here;
* `Work.UBBInputs8.A.integral_abox_comp_apply` (`∫_{abox N L}f(xᵢ) = (L³)^{N-1}∫_{acube L}f`)
  plus AM–GM `χ(x_p1)χ(x_p2) ≤ ½(χ(x_p1)²+χ(x_p2)²)` give the box integrals
  (`Work.UBBInputs8.A.integral_hlowDom_le`, `Work.UBBInputs8.A.integrableOn_hlowDom`,
  `Work.UBBInputs8.A.pairSet_card_cast_le`);
* the assembly uses the *unconditional* `norm_integral_le_integral_norm`
  (`−∫|f| ≤ ∫f`) and `integral_mono_of_nonneg`, so **no integrability of the `qLHSBIntegrand` is
  needed** — neither hypothesis nor side goal;
* `Work.UBBInputs8.A.tBwordB_nonneg` disposes of the kinetic word (`0 ≤ tBwordB` for `0 ≤ ε`, no
  sign hypothesis on `L`).

The resulting constant is
`C = sup_{abox} Φ² · (L³)^{N-1} · (μ·N·KL·(Ld)³ + ½·Bv/smallConvLower M·N²)`. -/
theorem exists_hlow_localised_of_bounded {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : Submission.BoseGases.IsRadial v)
    (hvb : ∃ Bv : ℝ, ∀ y : EuclideanSpace ℝ (Fin 3), |v y| ≤ Bv)
    {M : ℕ} (hM : 1 ≤ M) {d : ℕ} (hd : (0 : ℝ) < (d : ℝ))
    (hdR : ∀ L : ℝ, 1 ≤ L → R0 ≤ (L * (d : ℝ)) / 16)
    (hdRχ : ∀ L : ℝ, 1 ≤ L → R0 ≤ L * Submission.BoseGases.chiR0)
    {L : ℝ} (hL : 1 ≤ L) (N : ℕ) (Φ : Submission.BoseGases.CSBox N L)
    (ε c : ℝ) (hε : 0 ≤ ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : EuclideanSpace ℝ (Fin 3),
      - C * Work.SmallBoxSliding.chiMass M L (d : ℝ) u
        ≤ Work.SmallBoxTBWord.tBwordB N L (d : ℝ) ε c u (Φ : Submission.BoseGases.X N → ℝ)
          + Work.SmallBoxSliding.qLHSwordB h M L (d : ℝ) (Work.UBB.dens N L) u
              (Φ : Submission.BoseGases.X N → ℝ) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hμ : 0 ≤ Work.UBB.dens N L := by
    rw [Work.UBB.dens]; positivity
  obtain ⟨S, hSnn, hSΦ⟩ : ∃ S : ℝ, 0 ≤ S ∧
      ∀ x ∈ Submission.BoseGases.abox N L, ((Φ : Submission.BoseGases.X N → ℝ) x) ^ 2 ≤ S := by
    have hcont : Continuous (fun x : Submission.BoseGases.X N =>
        ((Φ : Submission.BoseGases.X N → ℝ) x) ^ 2) := Φ.contDiff.continuous.pow 2
    have hK : IsCompact (Submission.BoseGases.abox N L) :=
      Submission.BoseGases.abox_compact N hLpos
    obtain ⟨C₀, hC₀⟩ := IsCompact.exists_bound_of_continuousOn hK hcont.continuousOn
    refine ⟨max C₀ 0, le_max_right _ _, fun x hx => ?_⟩
    have h1 : ‖((Φ : Submission.BoseGases.X N → ℝ) x) ^ 2‖ ≤ C₀ := hC₀ x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at h1
    exact le_trans h1 (le_max_left _ _)
  obtain ⟨Bv, hBv⟩ := hvb
  have hBvnn : 0 ≤ Bv := le_trans (abs_nonneg (v 0)) (hBv 0)
  have hsc : 0 < Work.SmallBoxSliding.smallConvLower M := Work.SmallBoxSliding.smallConvLower_pos M
  set KP : ℝ := 2 * Bv / Work.SmallBoxSliding.smallConvLower M with hKPdef
  have hKPnn : 0 ≤ KP := by
    rw [hKPdef]; exact div_nonneg (mul_nonneg (by norm_num) hBvnn) hsc.le
  obtain ⟨K1, hK1nn, hK1⟩ := exists_fibre_wSmall1Pair_le_T (v := v) (h := h) (R0 := R0)
    (Bv := Bv) hv_supp hR0 hv hvrad hBv hM hd hdR hdRχ hL
  set C : ℝ := S * ((L ^ 3) ^ (N - 1) *
      (Work.UBB.dens N L * (N : ℝ) * K1 * (L * (d : ℝ)) ^ 3 + (1 / 2) * KP * (N : ℝ) ^ 2))
    with hCdef
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    have hA : 0 ≤ (L ^ 3) ^ (N - 1) := pow_nonneg (pow_nonneg hLpos.le 3) _
    have hB : 0 ≤ Work.UBB.dens N L * (N : ℝ) * K1 * (L * (d : ℝ)) ^ 3 :=
      mul_nonneg (mul_nonneg (mul_nonneg hμ (Nat.cast_nonneg N)) hK1nn)
        (pow_nonneg (mul_nonneg hLpos.le hd.le) 3)
    have hD : 0 ≤ (1 / 2) * KP * (N : ℝ) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hKPnn) (pow_nonneg (Nat.cast_nonneg N) 2)
    exact mul_nonneg hSnn (mul_nonneg hA (add_nonneg hB hD))
  refine ⟨C, hCnn, ?_⟩
  intro u
  have hpot : -(C * Work.SmallBoxSliding.chiMass M L (d : ℝ) u)
      ≤ Work.SmallBoxSliding.qLHSwordB h M L (d : ℝ) (Work.UBB.dens N L) u
          (Φ : Submission.BoseGases.X N → ℝ) := by
    set T : ℝ := ∫ x : ℝ³, Submission.BoseGases.chiSmallB M L (d : ℝ) u x with hTdef
    have hTnn : 0 ≤ T := by
      rw [hTdef]
      exact integral_nonneg (fun x => Submission.BoseGases.chiSmallB_nonneg M L (d : ℝ) u x)
    have hT2 : T ^ 2 ≤ Work.SmallBoxSliding.chiMass M L (d : ℝ) u * (L * (d : ℝ)) ^ 3 := by
      rw [hTdef]
      exact sq_integral_chiSmallB_le hM hLpos hd u
    have hfib : ∀ z : ℝ³,
        |∫ y in Submission.BoseGases.acube L,
          Submission.BoseGases.wSmall1Pair h M L (d : ℝ) u z y|
          ≤ K1 * T * Submission.BoseGases.chiSmallB M L (d : ℝ) u z := by
      intro z
      rw [hTdef]
      exact hK1 u z
    have hpair : ∀ x y : ℝ³,
        |Submission.BoseGases.wSmallPair M L (d : ℝ) u v x y|
          ≤ KP * Submission.BoseGases.chiSmallB M L (d : ℝ) u x
              * Submission.BoseGases.chiSmallB M L (d : ℝ) u y := by
      intro x y
      rw [hKPdef]
      exact abs_wSmallPair_chiB_le (v := v) (R0 := R0) (Bv := Bv) hv_supp hBv hM hLpos hd
        (hdR L hL) (hdRχ L hL) u x y
    have hpt := abs_qLHSBIntegrand_le (hM := hM) (hL := hLpos) (hd := hd) (hμ := hμ)
      (hS := hSnn) (hKL := hK1nn) (hKP := hKPnn) (hT := hTnn) u hSΦ hfib hpair
    have hdomInt : IntegrableOn (fun x : Submission.BoseGases.X N =>
        S * (Work.UBB.dens N L *
              (K1 * T * ∑ i : Fin N, Submission.BoseGases.chiSmallB M L (d : ℝ) u (x i))
            + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
                KP * Submission.BoseGases.chiSmallB M L (d : ℝ) u (x p.1)
                  * Submission.BoseGases.chiSmallB M L (d : ℝ) u (x p.2))))
        (Submission.BoseGases.abox N L) :=
      integrableOn_hlowDom (hM := hM) (hL := hLpos) (hd := hd) u
    have h3 : (∫ x in Submission.BoseGases.abox N L,
          S * (Work.UBB.dens N L *
                (K1 * T * ∑ i : Fin N, Submission.BoseGases.chiSmallB M L (d : ℝ) u (x i))
              + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
                  KP * Submission.BoseGases.chiSmallB M L (d : ℝ) u (x p.1)
                    * Submission.BoseGases.chiSmallB M L (d : ℝ) u (x p.2))))
        ≤ C * Work.SmallBoxSliding.chiMass M L (d : ℝ) u := by
      have hdom := integral_hlowDom_le (N := N) (hM := hM) (hL := hLpos) (hd := hd) (hμ := hμ)
        (hS := hSnn) (hKL := hK1nn) (hKP := hKPnn) (hT := hTnn) u hTdef hT2
      rw [hCdef]
      calc (∫ x in Submission.BoseGases.abox N L,
            S * (Work.UBB.dens N L *
                  (K1 * T * ∑ i : Fin N, Submission.BoseGases.chiSmallB M L (d : ℝ) u (x i))
                + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
                    KP * Submission.BoseGases.chiSmallB M L (d : ℝ) u (x p.1)
                      * Submission.BoseGases.chiSmallB M L (d : ℝ) u (x p.2))))
          ≤ S * ((L ^ 3) ^ (N - 1) *
              (Work.UBB.dens N L * (N : ℝ) * K1 * (L * (d : ℝ)) ^ 3
                + (1 / 2) * KP * (N : ℝ) ^ 2)
              * Work.SmallBoxSliding.chiMass M L (d : ℝ) u) := hdom
        _ = S * ((L ^ 3) ^ (N - 1) *
              (Work.UBB.dens N L * (N : ℝ) * K1 * (L * (d : ℝ)) ^ 3
                + (1 / 2) * KP * (N : ℝ) ^ 2))
              * Work.SmallBoxSliding.chiMass M L (d : ℝ) u := by ring
    have h2 : (∫ x in Submission.BoseGases.abox N L,
          |Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ) (Work.UBB.dens N L)
            (Φ : Submission.BoseGases.X N → ℝ) u x|)
        ≤ ∫ x in Submission.BoseGases.abox N L,
          S * (Work.UBB.dens N L *
                (K1 * T * ∑ i : Fin N, Submission.BoseGases.chiSmallB M L (d : ℝ) u (x i))
              + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
                  KP * Submission.BoseGases.chiSmallB M L (d : ℝ) u (x p.1)
                    * Submission.BoseGases.chiSmallB M L (d : ℝ) u (x p.2))) := by
      refine integral_mono_of_nonneg
        (μ := (volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N L))
        (f := fun x => |Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ) (Work.UBB.dens N L)
            (Φ : Submission.BoseGases.X N → ℝ) u x|)
        (g := fun x => S * (Work.UBB.dens N L *
                (K1 * T * ∑ i : Fin N, Submission.BoseGases.chiSmallB M L (d : ℝ) u (x i))
              + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
                  KP * Submission.BoseGases.chiSmallB M L (d : ℝ) u (x p.1)
                    * Submission.BoseGases.chiSmallB M L (d : ℝ) u (x p.2))))
        (ae_of_all _ (fun x => abs_nonneg _)) hdomInt ?_
      filter_upwards [ae_restrict_mem (Submission.BoseGases.abox_measurable N L)] with x hx
      exact hpt x hx
    have h1 : -(∫ x in Submission.BoseGases.abox N L,
          |Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ) (Work.UBB.dens N L)
            (Φ : Submission.BoseGases.X N → ℝ) u x|)
        ≤ ∫ x in Submission.BoseGases.abox N L,
          Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ) (Work.UBB.dens N L)
            (Φ : Submission.BoseGases.X N → ℝ) u x := by
      have hnorm := norm_integral_le_integral_norm
        (μ := (volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N L))
        (fun x => Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ) (Work.UBB.dens N L)
            (Φ : Submission.BoseGases.X N → ℝ) u x)
      have hneg : -‖∫ x, Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ) (Work.UBB.dens N L)
              (Φ : Submission.BoseGases.X N → ℝ) u x
            ∂((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N L))‖
          ≤ ∫ x, Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ) (Work.UBB.dens N L)
              (Φ : Submission.BoseGases.X N → ℝ) u x
            ∂((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N L)) := by
        have := (abs_le.mp (le_refl |∫ x, Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ)
            (Work.UBB.dens N L) (Φ : Submission.BoseGases.X N → ℝ) u x
            ∂((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N L))|)).1
        simpa [Real.norm_eq_abs] using this
      rw [show (∫ x, ‖Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ) (Work.UBB.dens N L)
              (Φ : Submission.BoseGases.X N → ℝ) u x‖
            ∂((volume : Measure (Submission.BoseGases.X N)).restrict (Submission.BoseGases.abox N L)))
          = ∫ x in Submission.BoseGases.abox N L,
              |Work.SmallBoxSliding.qLHSBIntegrand h M L (d : ℝ) (Work.UBB.dens N L)
                (Φ : Submission.BoseGases.X N → ℝ) u x| from by
        simp only [Real.norm_eq_abs]] at hnorm
      linarith [hnorm, hneg]
    have h2' := neg_le_neg h2
    have h3' : -(C * Work.SmallBoxSliding.chiMass M L (d : ℝ) u)
        ≤ -(∫ x in Submission.BoseGases.abox N L,
          S * (Work.UBB.dens N L *
                (K1 * T * ∑ i : Fin N, Submission.BoseGases.chiSmallB M L (d : ℝ) u (x i))
              + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
                  KP * Submission.BoseGases.chiSmallB M L (d : ℝ) u (x p.1)
                    * Submission.BoseGases.chiSmallB M L (d : ℝ) u (x p.2)))) := by linarith [h3]
    exact le_trans h3' (le_trans h2' h1)
  have hkin : 0 ≤ Work.SmallBoxTBWord.tBwordB N L (d : ℝ) ε c u
      (Φ : Submission.BoseGases.X N → ℝ) :=
    tBwordB_nonneg (N := N) L (d : ℝ) ε c hε u _
  linarith

end Work.UBBInputs8.A
