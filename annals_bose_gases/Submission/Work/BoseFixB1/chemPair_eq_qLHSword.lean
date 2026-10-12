import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBox.boxWordU_eq_boxForm_of_supp_radial
import Submission.Work.BoseBoxFix.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


/-
# FINDING — `Work.BoseFixB1.chemPair_eq_qLHSword` is **FALSE as stated**

> **Verdict: `declare_false`.**  The requested identity is the *integral-level* split of a
> single integral into its two summands, and it is missing the integrability hypotheses
> `IntegrableOn A (abox n ℓ)`, `IntegrableOn B (abox n ℓ)` of the two integrands (equivalently:
> a hypothesis making the two-body integrand integrable, e.g. `MemLp v 1` together with
> `tsupport v ⊆ ball 0 R`).  Without them Mathlib's Bochner integral is `0` on any
> non-integrable integrand (`MeasureTheory.integral_undef`), while the two sides of the
> requested identity split the *same* integrand in different ways, so they can disagree.
>
> **The repaired statement** — the same identity with the two `IntegrableOn` hypotheses added —
> is **proved, sorry-free**, below as
>
>     Work.BoseFixB1.chemPair_eq_qLHSword_of_integrable
>
> (and it is exactly `MeasureTheory.integral_add` + the pointwise identity of the brackets).
>
> **The finding was NOT caught by the pointwise analysis:** the *pointwise* identity of the
> brackets is true and is a proved corpus lemma (`Work.BoseBox.potBracketG_eq_potWordU`, which
> is `Work.BoseBox.bracket_qLHSword_eq_potWordU` at `wLoc ℓ · 0 = wPairC ℓ ·`): the `Σ_{i<j}` /
> `(1/2)Σ_{i≠j}` pair conventions agree because `hvrad` makes the kernel symmetric, and the box
> fibre `w1Fibre ℓ (wPairC ℓ (g₀ v h)) (xᵢ)` equals the whole-space fibre
> `∫_y wLoc ℓ (g₀ v h) 0 (xᵢ) y` because `χ_ℓ` vanishes off `acube ℓ` when `0 < ℓ`.  What fails
> is the passage **pointwise identity ⟹ integral identity**: the two sides are
> `∫ A + ∫ B` (LHS) and `∫ (A + B)` (RHS) for the same pair of functions `A`, `B`, and
> `MeasureTheory.integral_add` requires `Integrable A` **and** `Integrable B`.  The corpus is
> aware of exactly this gap elsewhere (`Work.BoseKinLoc.Word.boxFormB_eq_parts_of_integrable`
> carries the two `IntegrableOn` hypotheses; the sibling
> `Work.BoseKinLoc.Word.bddBelow_boxState_ratio_of_growth` does a case split on *whether* the
> chemical integrand is integrable, precisely because `boxFormB` is then `0` by
> `integral_undef`).

## Why `IntegrableOn B (abox n ℓ)` is *not* a consequence of the hypotheses

Here `A` and `B` are the two summands of `Work.BoseKinLoc.potWordU n v (g₀ v h) ℓ μ 0`, i.e.

    A x = (Φ x)² · ( −μ · Σᵢ ∫_y wLoc ℓ (g₀ v h) 0 (xᵢ) y )
    B x = (Φ x)² · ( Σ_{i<j} wLoc ℓ v 0 (xᵢ,xⱼ) ).

* `B` is (up to the bounded factor `Φ²` on the compact box) controlled by the kernel
  `wPairC ℓ v = wLoc ℓ v 0`, whose `lintegral` obeys the *sharp* corpus bound
  `Work.BoseFixB2.Pot.lintegral_wPairC_le`, whose hypothesis is exactly `Integrable h`
  (for `h := v`): the χ-renormalised kernel is integrable **iff** the numerator is.  Hence
  `B ∈ L¹` requires `v ∈ L¹`.
* `A` only involves `g₀ = v·(1−w₀)`, which is *much* nicer than `v`: the corpus's
  `Submission.ScatKernelChosen.g0_integrable` proves `g₀ ∈ L¹` from **nothing but**
  `tsupport v ⊆ ball 0 R` (plus `0 < R` and `ScatSol v`) — no `v ∈ L¹` hypothesis at all
  (this is what the corpus uses; `Work.BoseFixB2.Pot.potWordU_integrable` needs `MemLp v 1`
  *only* for the pair half).

So the two integrabilities are independent — in stark contrast to the *pair* conventions, which
the `hvrad` hypothesis does reconcile.

## The counterexample

`IsScatteringSolution w v` constrains `v` only through the product `v·(1−w)` (its only
occurrence is in `rhs_integrable : LocallyIntegrable (v·(1−w))` and in the integrand of the weak
equation).  Hence `v` is completely free on the level set `{w = 1}`, which can have positive
measure: take a radial `w₀ ∈ C_c^∞` with `w₀ ≡ 1` on `B(0,1)`, `w₀ ≡ 0` outside `B(0,2)`,
`0 ≤ w₀ ≤ 1`, concave and strictly decreasing on the annulus `1 < ‖x‖ < 2`, and put

    v x := ‖x‖^{−7}                    for ‖x‖ ≤ 1,
    v x := −2 Δw₀ x / (1 − w₀ x)       for 1 < ‖x‖ < 2   (well defined: w₀ < 1 there),
    v x := 0                           for ‖x‖ ≥ 2.

Then `v` is radial, non-negative, compactly supported (`tsupport v ⊆ ball 0 3`), and
`v·(1−w₀) = −2 Δw₀` **pointwise** (on `B(0,1)` both sides are `0` because `Δw₀ = 0` where `w₀`
is locally constant `1`; on the annulus it is the definition; outside it is `0 = 0`).  Hence
`−∫ w₀ Δφ = −∫ Δw₀ φ = (1/2) ∫ v(1−w₀) φ` for all `φ ∈ C_c^∞` (integration by parts; `w₀` is
`C²` with compact support), `w₀ → 0` at `cocompact`, and both `w₀` and `v(1−w₀) = −2Δw₀` are
locally integrable: so `IsScatteringSolution w₀ v` holds, and with `h := ⟨w₀, ·, ·⟩` we get
`Work.UBB.ScatSol v`.  But `v ∉ L¹` (`∫_{‖x‖<1} ‖x‖^{−7} dx = ∞`).

Now take `n = 2`, `Φ ≡ 1` (continuous), `μ = 1`, and `ℓ` large (`ℓ = 10`).

* **LHS.**  `pairPartB 2 v ℓ 1 ≡ 0`: its integrand is `wLoc ℓ v 0 (x₀,x₁)`, which is
  `≈ χ_ℓ(0)² ‖x₀−x₁‖^{−7}` near the *interior* point `x₀ = x₁ = 0`, whose `∫⁻` over `ℝ⁶`
  diverges as `∫_0 r^{−7} r⁵ dr = ∞`; so `B ∉ L¹` and `∫ B = 0` (`integral_undef`).
  Meanwhile the chemical integrand `A` *is* integrable: `g₀ = v(1 − Classical.choose h)` is in
  `L¹` (`g0_integrable`), and `A` is `Φ²` times the sum of the fibres
  `potBr ℓ (g₀) 0 (xᵢ) = ∫_y wLoc ℓ (g₀) 0 (xᵢ) y`, whose `∫⁻` satisfies
  `∫⁻_a ‖potBr … a‖ ≤ ∫⁻_{(a,y)} ‖wPairC ℓ g₀ a y‖ ≤ ℓ³ ∫|g₀| < ∞`
  (`lintegral_wPairC_le` + `enorm_integral_le_lintegral_enorm` + peeling) — the very estimate
  used for the chemical half in `Work.BoseFixB2.Pot.potWordU_integrable`.
  Moreover `g₀ ≥ 0` a.e. (`ScatT3.scattering_g_nonneg`, from `scattering_bounds_ae`: `w ≤ 1`
  a.e. because `v ≥ 0, radial, supported`) and `g₀ ≢ 0` (otherwise `∫ v(1−w) φ = 0` for all
  `φ`, so `Δw = 0` weakly, so `w = 0` a.e. by Weyl's lemma plus the cocompact limit `0`, and
  then `g₀ = v ≢ 0` on the unit ball — a contradiction).  Hence `potBr ℓ (g₀) 0 ≥ 0` and
  `≢ 0` on `acube ℓ`, so
  `chemPartB 2 (g₀) ℓ 1 (Φ ≡ 1) = −2·ℓ³·∫_{acube ℓ} potBr ℓ (g₀) 0 ≠ 0`.
* **RHS.**  `qLHSword 2 ℓ 1 (wPairC ℓ v) (wPairC ℓ (g₀)) (Φ ≡ 1)` is `∫ (A + B)`, and
  `A + B ∉ L¹` (`A ∈ L¹`, `B ∉ L¹`), so it is `0`.

So `chemPartB + pairPartB ≠ qLHSword`. ∎

## The repair (proved below, sorry-free)

Add `IntegrableOn` of the two integrands — in the consumer's context (`Work.BoseFixB1P.sbPot_integral_eq`,
`Work.BoseFixB1.potTelescope_fs`, where `hv1 : MemLp v 1` and
`hv_supp : tsupport v ⊆ ball 0 R` *are* available) these follow from
`Work.BoseFixB2.Pot.potWordU_integrable`'s two halves.  With them the proof is
`MeasureTheory.integral_add` plus the (already proved) pointwise identity.  Both are given below
as `chemPair_eq_qLHSword_of_integrable`.
-/
namespace Work.BoseFixB1

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false

/-- With translation parameter `u = 0` the localisation kernel `wLoc` *is* the χ-renormalised
two-body kernel `wPairC` (this is the definitional bridge that makes the requested identity
meaningful). -/
lemma wLoc_zero_eq_wPairC_local (ℓ : ℝ) (h : EuclideanSpace ℝ (Fin 3) → ℝ)
    (a b : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.wLoc ℓ h 0 a b = Submission.BoseGases.wPairC ℓ h a b := by
  rw [Submission.BoseGases.wPairC_apply]
  simp only [Submission.BoseGases.wLoc, Submission.BoseGases.wScaled,
    Submission.BoseGases.chiU, Submission.BoseGases.chiScale, sub_zero]

/-- **The pointwise identity of the two brackets.**  For `0 < ℓ` the bracket of
`qLHSword ℓ μ (wPairC ℓ v) (wPairC ℓ (g₀ v h))` (box fibres of `wPairC`, unordered pair sum
`(1/2) Σ_{p ∈ pairSet n}`) is the bracket of `potWordU` (whole-space fibres `∫_y wLoc ℓ · 0`,
ordered pair sum `Σ_{i<j}`) — for radial `v` (symmetry of the kernel) and `0 < ℓ`
(`χ_ℓ · 0 = wPairC ℓ ·`, and the box fibre at `u = 0` is the whole-space fibre). -/
lemma qLHSbracket_eq_potWordU_bracket {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hvrad : _root_.BoseGases.IsRadial v) {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {n : ℕ} (x : Submission.BoseGases.X n) :
    (- μ * (∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y))
        + (∑ ij : {ij : Fin n × Fin n // ij.1 < ij.2},
            Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2))
      = - μ * (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
            (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) (x i))
        + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
            Submission.BoseGases.wPairC ℓ v (x p.1) (x p.2)) := by
  -- the LHS *is* `potWordU` (definitionally), and the corpus pointwise identity expresses
  -- `potWordU` through the `wLoc`-spelling of the `qLHSword` bracket
  have hcorpus := Work.BoseBox.bracket_qLHSword_eq_potWordU (n := n) (ℓ := ℓ) (μ := μ)
    (v := v) (h := h) hℓ hvrad x
  have hfib : (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) (x i))
      = ∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
          (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) (x i) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold Submission.BoseGases.w1Fibre
    exact MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ)
      (fun y _ => wLoc_zero_eq_wPairC_local ℓ (Submission.BoseGases.g0 v h) (x i) y)
  have hpair : (∑ p ∈ Submission.BoseGases.pairSet n,
        Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
      = ∑ p ∈ Submission.BoseGases.pairSet n,
          Submission.BoseGases.wPairC ℓ v (x p.1) (x p.2) :=
    Finset.sum_congr rfl (fun p _ => wLoc_zero_eq_wPairC_local ℓ v (x p.1) (x p.2))
  calc (- μ * (∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y))
        + (∑ ij : {ij : Fin n × Fin n // ij.1 < ij.2},
            Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2))
      = Work.BoseKinLoc.potWordU n v (Submission.BoseGases.g0 v h) ℓ μ 0 x := rfl
    _ = - μ * (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
            (Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0) (x i))
          + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
              Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2)) := hcorpus.symm
    _ = - μ * (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
            (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) (x i))
          + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
              Submission.BoseGases.wPairC ℓ v (x p.1) (x p.2)) := by
        rw [hfib, hpair]

/-- **The repaired identity (proved).**  `chemPartB + pairPartB = qLHSword` holds as soon as the
two summand integrands are integrable on the box — which is exactly the missing hypothesis of the
requested statement.  The proof is `MeasureTheory.integral_add` together with the pointwise
identity `qLHSbracket_eq_potWordU_bracket`. -/
theorem chemPair_eq_qLHSword_of_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hvrad : _root_.BoseGases.IsRadial v) {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    (hA : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (-μ * (∑ i : Fin n, ∫ y : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)))
      (Submission.BoseGases.abox n ℓ))
    (hB : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 *
      (∑ ij : {ij : Fin n × Fin n // ij.1 < ij.2},
        Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2)))
      (Submission.BoseGases.abox n ℓ)) :
    Work.BoseKinLoc.chemPartB n (Submission.BoseGases.g0 v h) ℓ μ Φ
      + Work.BoseKinLoc.pairPartB n v ℓ Φ
      = Submission.BoseGases.qLHSword (N := n) ℓ μ (Submission.BoseGases.wPairC ℓ v)
          (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) Φ := by
  rw [show Work.BoseKinLoc.chemPartB n (Submission.BoseGases.g0 v h) ℓ μ Φ
        = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 * (-μ * (∑ i : Fin n,
            ∫ y : EuclideanSpace ℝ (Fin 3),
              Submission.BoseGases.wLoc ℓ (Submission.BoseGases.g0 v h) 0 (x i) y)) from rfl,
    show Work.BoseKinLoc.pairPartB n v ℓ Φ
        = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
            (∑ ij : {ij : Fin n × Fin n // ij.1 < ij.2},
              Submission.BoseGases.wLoc ℓ v 0 (x ij.1.1) (x ij.1.2)) from rfl]
  rw [← MeasureTheory.integral_add hA hB]
  rw [show Submission.BoseGases.qLHSword (N := n) ℓ μ (Submission.BoseGases.wPairC ℓ v)
        (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) Φ
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 *
          (- μ * (∑ i : Fin n, Submission.BoseGases.w1Fibre ℓ
              (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) (x i))
            + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet n,
                Submission.BoseGases.wPairC ℓ v (x p.1) (x p.2))) from rfl]
  refine MeasureTheory.setIntegral_congr_fun (Submission.BoseGases.abox_measurable n ℓ)
    (fun x _ => ?_)
  rw [← mul_add]
  rw [qLHSbracket_eq_potWordU_bracket h hvrad hℓ x]

/-- The requested statement, kept **verbatim** (`sorry` — see the header: it is FALSE without
the integrability hypotheses, supplied in `chemPair_eq_qLHSword_of_integrable`). -/
theorem chemPair_eq_qLHSword {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hvrad : _root_.BoseGases.IsRadial v) {ℓ μ : ℝ} (hℓ : 0 < ℓ)
    {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    Work.BoseKinLoc.chemPartB n (Submission.BoseGases.g0 v h) ℓ μ Φ
      + Work.BoseKinLoc.pairPartB n v ℓ Φ
      = Submission.BoseGases.qLHSword (N := n) ℓ μ (Submission.BoseGases.wPairC ℓ v)
          (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h)) Φ := by sorry

end Work.BoseFixB1
