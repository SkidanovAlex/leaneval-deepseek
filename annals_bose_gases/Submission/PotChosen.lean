import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Submission.PotWords
import Submission.WordInteg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5, S5c — the potential splitting (`lem:potsplit eq:potsplit`) with the
CHOSEN χ-renormalized kernels, at the L¹ level

`Submission.PotWords.potsplit_expect` proves the potential-energy splitting

    qLHSword ℓ μ w w1 Φ = q0word + q1word + q2word + q3word + q4word

for ABSTRACT kernels `w w1 w2 ω` satisfying the pointwise relations
`w1 = w·(1−ω)`, `w2 = w·(1−ω²)` and symmetries, under CONTINUITY hypotheses
(`hwc`, `homc`) on the kernels (continuity is used only to justify
integrability of the many word integrands over the compact centred box).

THIS module instantiates the splitting with the actual Fournais--Solovej
kernels of the problem (`eq:defW_12`, `eq:w_u`, `eq:3.5`):

    w(x,y)  := wPair(ℓ,v)(x,y)   = χ_ℓ(x)·v(x−y)/(χ⋆χ)_ℓ(x−y)·χ_ℓ(y)
    w₁(x,y) := wPair(ℓ,g₀)(x,y)  (g₀ := v(1−w₀) = the corpus `g`)
    w₂(x,y) := wPair(ℓ,g₂)(x,y)  (g₂ := g₀(1+w₀))
    ω(x,y)  := w₀(x−y)           (w₀ := the chosen scattering solution)

for which the kernel is NOT continuous (v is only L¹), so the PotWords
theorem does not apply directly.  Here the pointwise relations and
symmetries (KernelRel/KernelSym) are reused verbatim — they are total-
function identities — and every integrability step is re-proved from the
`L¹`-numerator machinery of `Submission.WordInteg`
(`integrableOn_bounded_mul_wPair_sub_abox`,
`integrableOn_wPair_abs_sub_abox`, `setIntegral_abs_sub_abox_le`),
`Submission.KernelFibreBound` (the one-body fibre bounds
`fibre_acube_abs_le`, `onebody_expect_abs_le`, `w1c_fibre_abs_le`,
`w2c_fibre_abs_le`), the a.e.-bounds of the chosen solution
(`ScatT3.scattering_bounds_ae`: `0 ≤ w₀ ≤ 1` a.e.), and the
`aP`/`aQ`-slot continuity/boundedness toolbox (`Q0Sector.aP_*`, compactness
`abox_compact`, `integrableOn_abox_of_continuous`).

## Standing hypotheses (chosen branch)

    (hℓ : 0 < ℓ) (μ : ℝ)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h  : ∃ w, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0)                -- dilute regime
    {Φ : XN N → ℝ} (hΦc : Continuous Φ)

Note `hRℓ` is needed because `WordInteg` bounds `|wPair| ≤ C·|h(x−y)|` only
when the numerator is supported in `ball 0 R` with `R ≤ ℓ·chiR0`
(`convScale ≥ 1/2` there, `ChiWitness.convScale_ge_half_ball`).

## The four headline statements (proofs go below)

  * `chosen_pair_pointwise` — the pointwise fragment identity
    `fgsum(i,j,x) = Φ(x)²·w(xᵢ,xⱼ)` for the chosen kernels (direct
    instantiation of `PotWords.potsplit_pair_pointwise`, which needs only the
    pointwise relations and symmetries — all available);
  * `chosen_pair_agree` — `pairInts(i,j) + pairInts(j,i) = ∫Φ²·w(xᵢ,xⱼ)`
    (integrate the pointwise identity; the only new content is the
    `IntegrableOn`-facts for the 7 fragment integrands in both orientations,
    obtained from `WordInteg` + `aP/aQ`-boundedness + a.e.-bounds on `w₀`);
  * `chosen_mu_agree` — the μ-slot-sum identity
    `Σᵢ muP + 2Σᵢ muQP + Σᵢ muQ = Σᵢ muPhi` for `w1 := wPair(g₀)` (each
    `mu*`-integrand is a bounded slot product against the bounded fibre
    `∫_{acube}w₁(xᵢ,·)`, integrable by `KernelFibreBound`);
  * `potsplit_chosen` — the main identity (assembled from the pair
    fragments as in `PotWords.potsplit_expect`: every q-word is a finite sum
    over `pairSet N` of `fg`-integrals plus the μ-slot sums; use
    `chosen_pair_agree` over the two orientations and `chosen_mu_agree`).

PROOF ROUTE for the child (read `Submission/PotWords.lean` carefully; the
structure below mirrors it):

1. (Integrability helpers — you may state and prove as many as you need.)
   For `h : ℝ³ → ℝ` with `hi : Integrable h` and
   `hsupp : ∀ z, R ≤ ‖z‖ → h z = 0`, `hℓ : 0 < ℓ`, `hRℓ : R ≤ ℓ·chiR0`,
   `i j : Fin N`, `hij : i ≠ j`, continuous `Φ`, prove
   `IntegrableOn (fun x => <slot product of aP/aQ factors at x> *
     wPair ℓ h (x i) (x j)) (abox N ℓ) volume`
   by `WordInteg.integrableOn_bounded_mul_wPair_sub_abox`: the slot product
   is continuous on the compact box hence bounded
   (`abox_compact`, `IsCompact.exists_bound_of_continuousOn`; the slot
   functions `aP ℓ i (… Φ)`, `aQ ℓ i (… Φ)` are continuous by
   `Q0Sector.aP_continuous`/`aQ_continuous` since `Φ` is continuous).
   Numerator integrability/support: `v` via `Potential.v_integrable
   hv_memL1` + `PotSupport.v_eq_zero_of_norm_ge`; `g₀` via
   `ScatKernelChosen.g0_integrable`/`g0_zero_of_norm_ge`; `g₂` via
   `g2_integrable`/`g2_zero_of_norm_ge`.
   For the `fg4` integrand (contains `q4B` with the factor
   `ω(xᵢ,xⱼ) = w₀(xᵢ−xⱼ)`): `w₀` is only a.e. bounded (`0 ≤ w₀ ≤ 1` a.e.:
   `ScatT3.scattering_bounds_ae`), so `q4B`-expressions are a.e.-bounded on
   `abox N ℓ` (pull the a.e.-bound of `w₀` back along the linear map
   `x ↦ xᵢ − xⱼ`; preimages of null sets under linear maps are null);
   then apply the same `WordInteg` bounded-mul lemma with the a.e. bound.
   For the μ-terms: the fibre `x ↦ ∫ y in acube ℓ, wPair ℓ (g0 v h) x y` is
   bounded by `KernelFibreBound.fibre_acube_abs_le` (via `w1c_fibre_abs_le`);
   products with continuous slot squares/crosses are integrable on the
   finite-measure box (`abox_lt_top`).
2. `chosen_pair_pointwise`: `exact potsplit_pair_pointwise hℓ hij
   (wPairC_v_sym hvrad ℓ) (omC_chosen_sym h) (w1rel_chosen h ℓ)
   (w2rel_chosen h ℓ) hΦc x`.
3. `chosen_pair_agree`: `pairInts(i,j) + pairInts(j,i)` unfolds to the sum
   of the 14 fragment integrals; re-associate with `← integral_add`
   (needs each fragment integrable, step 1) to get
   `∫ x, fgsum … i j x`, then `rw [← chosen_pair_pointwise]`.
4. `chosen_mu_agree`: copy `PotWords.mu_sum_agree` / `potsplit_mu_agree`
   with the integrability hypotheses from step 1 (the pointwise algebra
   `(Pᵢ+Qᵢ)² = Pᵢ+Qᵢ`-style expansions in `potsplit_mu_agree` are
   continuity-free).
5. `potsplit_chosen`: copy the `PotWords.potsplit_expect` assembly:
   split `qLHSword` into the μ-part and the pair part
   (`∫ Φ²·(−μΣᵢw1Fibre(xᵢ)) + ½Σ_p∫Φ²·w(x_p1,x_p2)` — note the qLHSword
   pair part is over ordered pairs in `pairSet N`); show the sum of the five
   words' pair parts equals `Σ_p pairInts(p.1,p.2)` (each q-word's pair part
   equals `Σ_p ∫fgₖ(p)` by its definition — mirror
   `PotWords.pair_part_sum_eq`, whose steps are `Finset.mul_sum`,
   `← integral_const_mul`, `integral_congr_ae`, `ring` and need the
   integrabilities of step 1), then use `chosen_pair_agree` +
   `PotWords.pairSet_swap_sum` to identify
   `Σ_p pairInts(p.1,p.2) = (1/2)·Σ_p ∫Φ²·w(x_p1,x_p2)` (mirror the
   `hpairsum` calc-block of `potsplit_expect`); the μ-sums of the words are
   `−μ(ΣᵢmuP + 2ΣᵢmuQP + ΣᵢmuQ) = −μΣᵢmuPhi` by `chosen_mu_agree`, which
   is exactly the qLHSword μ-part.  `ring` finishes.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)


/-! ## L¹-integrability machinery for the chosen kernels -/

/-- A continuous factor times `wPair(ℓ,h)(xᵢ,xⱼ)` is integrable over the box:
the factor is bounded on the compact centred box (WordInteg bounded-mul lemma). -/
lemma integrableOn_slot_wPair {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) {h : ℝ³ → ℝ}
    (hh : Integrable h) (hsupp : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0)
    (hRℓ : R ≤ ℓ * chiR0) {i j : Fin N} (hij : i ≠ j)
    {S : XN N → ℝ} (hSc : Continuous S) :
    IntegrableOn (fun x : XN N => S x * wPair ℓ h (x i) (x j)) (abox N ℓ) volume := by
  have hcS : ContinuousOn S (abox N ℓ) := hSc.continuousOn
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ) (f := S) hcS
  have hB0 : 0 ≤ B := by
    have hb := hB (0 : XN N) (zero_mem_abox hℓ.le)
    exact le_trans (norm_nonneg (S (0 : XN N))) hb
  have hgm : AEStronglyMeasurable S (volume.restrict (abox N ℓ)) := hSc.aestronglyMeasurable
  have hgb : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |S x| ≤ B := by
    rw [ae_restrict_iff' (abox_measurable N ℓ)]
    exact ae_of_all _ (by
      intro x hx
      simpa [Real.norm_eq_abs] using hB x hx)
  exact integrableOn_bounded_mul_wPair_sub_abox hℓ hh hsupp hRℓ i j hij hgm hB0 hgb

/-- The acube-fibre `z ↦ ∫_{acube ℓ} wPair(ℓ,h)(z,·)` is a.e. strongly
measurable over the cube, for an integrable numerator `h`. -/
lemma fibre_acube_aem {ℓ : ℝ} {h : ℝ³ → ℝ} (hh : Integrable h) :
    AEStronglyMeasurable (fun z : ℝ³ => ∫ y in acube ℓ, wPair ℓ h z y)
      (volume.restrict (acube ℓ)) := by
  have hU : AEStronglyMeasurable (wPairU ℓ h)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := aesm_wPairU_prod hh
  have hle : ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube ℓ))) ≤
      (volume : Measure ℝ³).prod (volume : Measure ℝ³) := by
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have hU' : AEStronglyMeasurable (wPairU ℓ h)
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube ℓ))) :=
    hU.mono_measure hle
  have hF : AEStronglyMeasurable (fun z : ℝ³ => ∫ y : ℝ³, wPairU ℓ h (z, y)
        ∂((volume : Measure ℝ³).restrict (acube ℓ))) (volume : Measure ℝ³) := by
    exact AEStronglyMeasurable.integral_prod_right'
      (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³).restrict (acube ℓ)) hU'
  have hEq : (fun z : ℝ³ => ∫ y : ℝ³, wPairU ℓ h (z, y)
        ∂((volume : Measure ℝ³).restrict (acube ℓ))) =ᵐ[volume]
      fun z : ℝ³ => ∫ y in acube ℓ, wPair ℓ h z y := by
    apply ae_of_all
    intro z
    apply integral_congr_ae
    filter_upwards with y
    rfl
  exact (AEStronglyMeasurable.congr hF hEq).mono_measure
    (Measure.restrict_le_self : (volume : Measure ℝ³).restrict (acube ℓ) ≤ volume)

/-- Pulling an a.e. strongly measurable cube function back along coordinate
`i` to the full `N`-box. -/
lemma aem_comp_coord' {N : ℕ} {ℓ : ℝ} (i : Fin N) {g : ℝ³ → ℝ}
    (hgm : AEStronglyMeasurable g (volume.restrict (acube ℓ))) :
    AEStronglyMeasurable (fun x : XN N => g (x i)) (volume.restrict (abox N ℓ)) := by
  let μ' : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube ℓ)
  let m : ℝ³ → ℝ := AEStronglyMeasurable.mk g hgm
  have hsm : StronglyMeasurable m := hgm.stronglyMeasurable_mk
  have hwitness : StronglyMeasurable (fun x : XN N => m (x i)) := by
    refine StronglyMeasurable.comp_measurable hsm ?_
    fun_prop
  refine ⟨fun x : XN N => m (x i), hwitness, ?_⟩
  change ∀ᵐ x ∂(volume.restrict (abox N ℓ)), g (x i) = m (x i)
  rw [ae_iff]
  have hA0 : μ' {z : ℝ³ | g z ≠ m z} = 0 := by
    dsimp [μ', m]
    simpa using (ae_iff.mp hgm.ae_eq_mk)
  have hpi : (Measure.pi (fun _ : Fin N => μ')) {x : XN N | g (x i) ≠ m (x i)} = 0 := by
    rw [show {x : XN N | g (x i) ≠ m (x i)} =
        (Set.univ : Set (Fin N)).pi (fun j : Fin N =>
          if j = i then {z : ℝ³ | g z ≠ m z} else Set.univ) by
      ext x
      simp]
    rw [Measure.pi_pi (μ := fun _ : Fin N => μ')]
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · simpa using hA0
  simpa [μ', restrict_abox_eq_pi] using hpi

/-- The `w₁`-fibre composed with the `i`-coordinate is a.e. strongly
measurable on the full box (numerator integrable). -/
lemma w1Fibre_coord_aem {N : ℕ} {ℓ : ℝ} {h : ℝ³ → ℝ} (hh : Integrable h)
    (i : Fin N) :
    AEStronglyMeasurable (fun x : XN N => w1Fibre ℓ (wPairC ℓ h) (x i))
      (volume.restrict (abox N ℓ)) := by
  have hfac := fibre_acube_aem (ℓ := ℓ) (h := h) hh
  have hfc := aem_comp_coord' (N := N) (ℓ := ℓ) i hfac
  simpa [w1Fibre, wPairC] using hfc

/-- A continuous slot against a measurable, cube-bounded fibre
`S x · F (x i)` is integrable over the box. -/
lemma integrableOn_slot_fibre {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N)
    {F : ℝ³ → ℝ} (hFm : AEStronglyMeasurable F (volume.restrict (acube ℓ)))
    {C : ℝ} (hC : ∀ z ∈ acube ℓ, |F z| ≤ C)
    {S : XN N → ℝ} (hSc : Continuous S) :
    IntegrableOn (fun x : XN N => S x * F (x i)) (abox N ℓ) volume := by
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ) (f := S) hSc.continuousOn
  have hB0 : 0 ≤ B := by
    have hb := hB (0 : XN N) (zero_mem_abox hℓ.le)
    exact le_trans (norm_nonneg (S (0 : XN N))) hb
  have hA : AEStronglyMeasurable (fun x : XN N => S x * F (x i))
      (volume.restrict (abox N ℓ)) := by
    exact hSc.aestronglyMeasurable.mul (aem_comp_coord' (N := N) (ℓ := ℓ) i hFm)
  have hbnd : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), ‖S x * F (x i)‖ ≤ B * C := by
    rw [ae_restrict_iff' (abox_measurable N ℓ)]
    apply ae_of_all
    intro x hx
    have hS : |S x| ≤ B := by simpa [Real.norm_eq_abs] using hB x hx
    have hF : |F (x i)| ≤ C := hC (x i) (hx i)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hS hF (abs_nonneg _) hB0
  exact IntegrableOn.of_bound (abox_lt_top N ℓ hℓ.le) hA (B * C) hbnd

/-- acube-fibre bound for the `g₀`-numerator in the chosen branch. -/
lemma w1c_fibre_acube_abs_le {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) (x : ℝ³) :
    |∫ y in acube ℓ, wPair ℓ (g0 v h) x y| ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
  have hbnd := fibre_acube_abs_le (h := g0 v h) hℓ (le_of_lt hR) hRℓ
    (g0_integrable hR hv_supp h) (fun z hz => g0_zero_of_norm_ge hv_supp hz h) x
  have hnn : ∀ᵐ z : ℝ³, 0 ≤ g0 v h z := g0_nonneg_ae hR hv_nonneg hvrad hv_supp h
  have hEq : (∫ z : ℝ³, |g0 v h z|) = ∫ z : ℝ³, g0 v h z := by
    apply integral_congr_ae
    filter_upwards [hnn] with z hz
    exact abs_of_nonneg hz
  rw [hEq, g0_integral hR hv_supp h] at hbnd
  exact hbnd

/-- Pulling an a.e. predicate on `ℝ³` back along `x ↦ xᵢ − xⱼ` to the box. -/
lemma ae_pair_pullback {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {p : ℝ³ → Prop} (hp : ∀ᵐ z ∂(volume : Measure ℝ³), p z) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)), p (x i - x j) := by
  rw [ae_iff]
  have hN : (volume : Measure ℝ³) {z : ℝ³ | ¬ p z} = 0 := by
    rw [← ae_iff]
    exact hp
  rcases exists_measurable_superset_of_null hN with ⟨t, hNt, htm, ht0⟩
  have hpre : (volume.restrict (abox N ℓ)) {x : XN N | x i - x j ∈ t} = 0 :=
    abox_null_preimage_pair hℓ htm ht0 i j hij
  have hfail : (volume.restrict (abox N ℓ)) {x : XN N | ¬ p (x i - x j)} = 0 := by
    have hsub : {x : XN N | ¬ p (x i - x j)} ⊆ {x : XN N | x i - x j ∈ t} := by
      intro x hx
      exact hNt hx
    exact le_antisymm (by
      calc
        (volume.restrict (abox N ℓ)) {x : XN N | ¬ p (x i - x j)}
            ≤ (volume.restrict (abox N ℓ)) {x : XN N | x i - x j ∈ t} := measure_mono hsub
        _ = 0 := hpre) (by positivity)
  simpa using hfail

/-- `x ↦ w₀(xᵢ−xⱼ)` is a.e. strongly measurable on the box (from local
integrability of the scattering solution). -/
lemma w0_diff_aem {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {w0 : ℝ³ → ℝ} (hw0li : LocallyIntegrable w0) :
    AEStronglyMeasurable (fun x : XN N => w0 (x i - x j))
      (volume.restrict (abox N ℓ)) := by
  have hwaem : AEStronglyMeasurable w0 (volume : Measure ℝ³) :=
    MeasureTheory.LocallyIntegrable.aestronglyMeasurable hw0li
  let m : ℝ³ → ℝ := AEStronglyMeasurable.mk w0 hwaem
  have hsm : StronglyMeasurable m := hwaem.stronglyMeasurable_mk
  have hwitness : StronglyMeasurable (fun x : XN N => m (x i - x j)) := by
    refine StronglyMeasurable.comp_measurable hsm ?_
    fun_prop
  refine ⟨fun x : XN N => m (x i - x j), hwitness, ?_⟩
  change ∀ᵐ x ∂(volume.restrict (abox N ℓ)), w0 (x i - x j) = m (x i - x j)
  rw [ae_iff]
  have hN : (volume : Measure ℝ³) {z : ℝ³ | w0 z ≠ m z} = 0 := by
    rw [← ae_iff]
    exact hwaem.ae_eq_mk
  rcases exists_measurable_superset_of_null hN with ⟨t, hNt, htm, ht0⟩
  have hpre : (volume.restrict (abox N ℓ)) {x : XN N | x i - x j ∈ t} = 0 :=
    abox_null_preimage_pair hℓ htm ht0 i j hij
  have hfail : (volume.restrict (abox N ℓ))
      {x : XN N | w0 (x i - x j) ≠ m (x i - x j)} = 0 := by
    have hsub : {x : XN N | w0 (x i - x j) ≠ m (x i - x j)} ⊆
        {x : XN N | x i - x j ∈ t} := by
      intro x hx
      apply hNt
      intro hEq
      exact hx (by rw [hEq])
    exact le_antisymm (by
      calc
        (volume.restrict (abox N ℓ)) {x : XN N | w0 (x i - x j) ≠ m (x i - x j)}
            ≤ (volume.restrict (abox N ℓ)) {x : XN N | x i - x j ∈ t} := measure_mono hsub
        _ = 0 := hpre) (by positivity)
  simpa using hfail

/-- Chosen-branch pointwise fragment identity: at every `x`, the combined
two-orientation word fragments at `(xᵢ,xⱼ)` equal `Φ(x)²·wPair(ℓ,v)(xᵢ,xⱼ)`. -/
lemma chosen_pair_pointwise {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hvrad : IsRadial v)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {Φ : XN N → ℝ} (hΦc : Continuous Φ) {i j : Fin N} (hij : i ≠ j) (x : XN N) :
    fgsum ℓ (wPairC ℓ v) (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h))
        (omC (Classical.choose h)) Φ i j x =
      (Φ x) ^ 2 * wPairC ℓ v (x i) (x j) := by
  exact potsplit_pair_pointwise hℓ hij (wPairC_v_sym hvrad ℓ) (omC_chosen_sym h)
    (w1rel_chosen h ℓ) (w2rel_chosen h ℓ) hΦc x


/-! ## Fragment integrability over the box (chosen kernels) -/

/-- `fg0` integrable over the box (w₂ := wPair(ℓ,g₂)). -/
lemma integrableOn_fg0_chosen {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ i j x) (abox N ℓ) volume := by
  have hSc : Continuous (fun x : XN N => (1 / 2) * (aP ℓ i (aP ℓ j Φ) x) ^ 2) := by
    have hc : Continuous (aP ℓ i (aP ℓ j Φ)) := aP_continuous hℓ i (aP_continuous hℓ j hΦc)
    fun_prop
  simpa [fg0, wPairC] using
    (integrableOn_slot_wPair (h := g2 v h) hℓ (g2_integrable hR hv_nonneg hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) hRℓ hij hSc)

/-- `fg1` integrable over the box (w₂ := wPair(ℓ,g₂)). -/
lemma integrableOn_fg1_chosen {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun x : XN N => fg1 ℓ (wPairC ℓ (g2 v h)) Φ i j x) (abox N ℓ) volume := by
  have hSc : Continuous (fun x : XN N =>
      2 * (aP ℓ i (aQ ℓ j Φ) x) * (aP ℓ i (aP ℓ j Φ) x)) := by
    have hc1 : Continuous (aP ℓ i (aQ ℓ j Φ)) := aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
    have hc2 : Continuous (aP ℓ i (aP ℓ j Φ)) := aP_continuous hℓ i (aP_continuous hℓ j hΦc)
    fun_prop
  simpa [fg1, wPairC] using
    (integrableOn_slot_wPair (h := g2 v h) hℓ (g2_integrable hR hv_nonneg hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) hRℓ hij hSc)

/-- `fg2a` integrable over the box (w₂ := wPair(ℓ,g₂)). -/
lemma integrableOn_fg2a_chosen {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun x : XN N => fg2a ℓ (wPairC ℓ (g2 v h)) Φ i j x) (abox N ℓ) volume := by
  have hSc : Continuous (fun x : XN N =>
      (aP ℓ i (aQ ℓ j Φ) x) * (aP ℓ j (aQ ℓ i Φ) x)) := by
    have hc1 : Continuous (aP ℓ i (aQ ℓ j Φ)) := aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
    have hc2 : Continuous (aP ℓ j (aQ ℓ i Φ)) := aP_continuous hℓ j (aQ_continuous hℓ i hΦc)
    fun_prop
  simpa [fg2a, wPairC] using
    (integrableOn_slot_wPair (h := g2 v h) hℓ (g2_integrable hR hv_nonneg hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) hRℓ hij hSc)

/-- `fg2b` integrable over the box (w₂ := wPair(ℓ,g₂)). -/
lemma integrableOn_fg2b_chosen {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun x : XN N => fg2b ℓ (wPairC ℓ (g2 v h)) Φ i j x) (abox N ℓ) volume := by
  have hSc : Continuous (fun x : XN N =>
      (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aP ℓ i Φ) x)) := by
    have hc1 : Continuous (aP ℓ i (aQ ℓ j Φ)) := aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
    have hc2 : Continuous (aQ ℓ j (aP ℓ i Φ)) := aQ_continuous hℓ j (aP_continuous hℓ i hΦc)
    fun_prop
  simpa [fg2b, wPairC] using
    (integrableOn_slot_wPair (h := g2 v h) hℓ (g2_integrable hR hv_nonneg hvrad hv_supp h)
      (fun z hz => g2_zero_of_norm_ge hv_supp hz h) hRℓ hij hSc)

/-- `fg2c` integrable over the box (w₁ := wPair(ℓ,g₀)). -/
lemma integrableOn_fg2c_chosen {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun x : XN N => fg2c ℓ (wPairC ℓ (g0 v h)) Φ i j x) (abox N ℓ) volume := by
  have hSc : Continuous (fun x : XN N =>
      (aP ℓ i (aP ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x)) := by
    have hc1 : Continuous (aP ℓ i (aP ℓ j Φ)) := aP_continuous hℓ i (aP_continuous hℓ j hΦc)
    have hc2 : Continuous (aQ ℓ j (aQ ℓ i Φ)) := aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)
    fun_prop
  simpa [fg2c, wPairC] using
    (integrableOn_slot_wPair (h := g0 v h) hℓ (g0_integrable hR hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h) hRℓ hij hSc)

/-- `fg3` integrable over the box (w₁ := wPair(ℓ,g₀)). -/
lemma integrableOn_fg3_chosen {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun x : XN N => fg3 ℓ (wPairC ℓ (g0 v h)) Φ i j x) (abox N ℓ) volume := by
  have hSc : Continuous (fun x : XN N =>
      2 * (aP ℓ i (aQ ℓ j Φ) x) * (aQ ℓ j (aQ ℓ i Φ) x)) := by
    have hc1 : Continuous (aP ℓ i (aQ ℓ j Φ)) := aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
    have hc2 : Continuous (aQ ℓ j (aQ ℓ i Φ)) := aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)
    fun_prop
  simpa [fg3, wPairC] using
    (integrableOn_slot_wPair (h := g0 v h) hℓ (g0_integrable hR hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h) hRℓ hij hSc)

/-- `fg4` integrable over the box (w := wPair(ℓ,v), ω := w₀(xᵢ−xⱼ)):
`q4B` is a.e. bounded (by `0 ≤ w₀ ≤ 1` a.e. pulled back to the box) and
a.e. strongly measurable (the scattering solution is locally integrable). -/
lemma integrableOn_fg4_chosen {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun x : XN N => fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ i j x)
      (abox N ℓ) volume := by
  let w0 : ℝ³ → ℝ := Classical.choose h
  have hrad₀ : IsRadial w0 := (w0_spec h).1
  have hscat₀ : IsScatteringSolution w0 v := (w0_spec h).2
  have hbnds := scattering_bounds_ae (w := w0) hR hv_nonneg hvrad hv_supp hrad₀ hscat₀
  have hw0ge0_full : ∀ᵐ z : ℝ³, 0 ≤ w0 z := hbnds.1
  have hw0le1_full : ∀ᵐ z : ℝ³, w0 z ≤ 1 := hbnds.2
  have hw0ge0 : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), 0 ≤ w0 (x i - x j) :=
    ae_pair_pullback hℓ hij hw0ge0_full
  have hw0le1 : ∀ᵐ x ∂(volume.restrict (abox N ℓ)), w0 (x i - x j) ≤ 1 :=
    ae_pair_pullback hℓ hij hw0le1_full
  have hw0li : LocallyIntegrable w0 := hscat₀.lhs_integrable
  have hw0aem : AEStronglyMeasurable (fun x : XN N => w0 (x i - x j))
      (volume.restrict (abox N ℓ)) := w0_diff_aem hℓ hij hw0li
  -- continuous parts of q4B
  have hDc : Continuous (aQ ℓ j (aQ ℓ i Φ)) := aQ_continuous hℓ j (aQ_continuous hℓ i hΦc)
  have hTc : Continuous (fun x : XN N =>
      (aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)) := by
    have hc1 : Continuous (aP ℓ j (aP ℓ i Φ)) := aP_continuous hℓ j (aP_continuous hℓ i hΦc)
    have hc2 : Continuous (aP ℓ j (aQ ℓ i Φ)) := aP_continuous hℓ j (aQ_continuous hℓ i hΦc)
    have hc3 : Continuous (aQ ℓ j (aP ℓ i Φ)) := aQ_continuous hℓ j (aP_continuous hℓ i hΦc)
    fun_prop
  have hGc : Continuous (fun x : XN N => |aQ ℓ j (aQ ℓ i Φ) x|
      + |(aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)|) := by fun_prop
  obtain ⟨B4, hB4⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ)
    (f := fun x : XN N => |aQ ℓ j (aQ ℓ i Φ) x|
      + |(aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)|)
    hGc.continuousOn
  have hB40 : 0 ≤ B4 := by
    have hb := hB4 (0 : XN N) (zero_mem_abox hℓ.le)
    exact le_trans (norm_nonneg _) hb
  -- pointwise (on the box) |q4B| ≤ |D| + |T| ≤ B4 once |w₀| ≤ 1
  have hq4bnd : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      |q4B ℓ (omC w0) Φ (i, j) x| ≤ B4 := by
    rw [ae_restrict_iff' (abox_measurable N ℓ)]
    filter_upwards [(ae_restrict_iff' (abox_measurable N ℓ)).mp hw0ge0,
      (ae_restrict_iff' (abox_measurable N ℓ)).mp hw0le1] with x hge0 hle1
    intro hx
    have hB4x : |aQ ℓ j (aQ ℓ i Φ) x|
        + |(aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)| ≤ B4 := by
      have hb := hB4 x hx
      have hGpos : 0 ≤ |aQ ℓ j (aQ ℓ i Φ) x|
          + |(aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x)| :=
        add_nonneg (abs_nonneg _) (abs_nonneg _)
      simpa [Real.norm_eq_abs, abs_of_nonneg hGpos] using hb
    have hOabs : |w0 (x i - x j)| ≤ 1 := by
      rw [abs_of_nonneg (hge0 hx)]
      exact hle1 hx
    unfold q4B omC
    calc
      |aQ ℓ j (aQ ℓ i Φ) x
          + w0 (x i - x j) * ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x)
            + (aQ ℓ j (aP ℓ i Φ) x))|
          ≤ |aQ ℓ j (aQ ℓ i Φ) x|
              + |w0 (x i - x j) * ((aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x)
                + (aQ ℓ j (aP ℓ i Φ) x))| := abs_add_le _ _
      _ ≤ |aQ ℓ j (aQ ℓ i Φ) x|
          + |w0 (x i - x j)| * |(aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x)
              + (aQ ℓ j (aP ℓ i Φ) x)| := by
            rw [abs_mul]
      _ ≤ |aQ ℓ j (aQ ℓ i Φ) x| + |(aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x)
              + (aQ ℓ j (aP ℓ i Φ) x)| := by
            have h1 : |w0 (x i - x j)| * |(aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x)
                + (aQ ℓ j (aP ℓ i Φ) x)| ≤ 1 * |(aP ℓ j (aP ℓ i Φ) x) + (aP ℓ j (aQ ℓ i Φ) x)
                + (aQ ℓ j (aP ℓ i Φ) x)| :=
              mul_le_mul_of_nonneg_right hOabs (abs_nonneg _)
            linarith
      _ ≤ B4 := by linarith
  -- a.e. strong measurability of the slot
  have hq4aem : AEStronglyMeasurable (fun x : XN N => q4B ℓ (omC w0) Φ (i, j) x)
      (volume.restrict (abox N ℓ)) := by
    have h1 : AEStronglyMeasurable (fun x : XN N => aQ ℓ j (aQ ℓ i Φ) x)
        (volume.restrict (abox N ℓ)) := hDc.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun x : XN N => (aP ℓ j (aP ℓ i Φ) x)
        + (aP ℓ j (aQ ℓ i Φ) x) + (aQ ℓ j (aP ℓ i Φ) x))
        (volume.restrict (abox N ℓ)) := hTc.aestronglyMeasurable
    unfold q4B omC
    exact h1.add (hw0aem.mul h2)
  have hsaem : AEStronglyMeasurable (fun x : XN N => (1 / 2) * (q4B ℓ (omC w0) Φ (i, j) x) ^ 2)
      (volume.restrict (abox N ℓ)) := by
    exact (hq4aem.pow 2).const_mul (1 / 2)
  have hsbnd : ∀ᵐ x ∂(volume.restrict (abox N ℓ)),
      |(1 / 2) * (q4B ℓ (omC w0) Φ (i, j) x) ^ 2| ≤ (1 / 2) * B4 ^ 2 := by
    filter_upwards [hq4bnd] with x hx
    have hle : |q4B ℓ (omC w0) Φ (i, j) x| ^ 2 ≤ B4 ^ 2 := by
      exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    calc
      |(1 / 2) * (q4B ℓ (omC w0) Φ (i, j) x) ^ 2|
          = (1 / 2) * |q4B ℓ (omC w0) Φ (i, j) x| ^ 2 := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_pow]
      _ ≤ (1 / 2) * B4 ^ 2 := by
            exact mul_le_mul_of_nonneg_left hle (by norm_num)
  have hB : 0 ≤ (1 / 2) * B4 ^ 2 := by positivity
  have hmain := integrableOn_bounded_mul_wPair_sub_abox (h := v) hℓ
    (v_integrable hv_memL1) (fun z hz => v_eq_zero_of_norm_ge hv_supp hz) hRℓ i j hij
    hsaem hB hsbnd
  simpa [fg4, wPairC] using hmain

/-- Chosen-branch pair agreement: the two orientations of the word fragments
together give the full `w`-expectation over the pair. -/
theorem chosen_pair_agree {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    pairInts ℓ (wPairC ℓ v) (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h))
        (omC (Classical.choose h)) Φ i j
      + pairInts ℓ (wPairC ℓ v) (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h))
        (omC (Classical.choose h)) Φ j i
    = ∫ x in abox N ℓ, (Φ x) ^ 2 * wPairC ℓ v (x i) (x j) := by
  -- integrability of the fourteen fragment integrands
  have i0 : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ i j x)
      (abox N ℓ) volume :=
    integrableOn_fg0_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hij
  have i1 : IntegrableOn (fun x : XN N => fg1 ℓ (wPairC ℓ (g2 v h)) Φ i j x)
      (abox N ℓ) volume :=
    integrableOn_fg1_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hij
  have i2 : IntegrableOn (fun x : XN N => fg2a ℓ (wPairC ℓ (g2 v h)) Φ i j x)
      (abox N ℓ) volume :=
    integrableOn_fg2a_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hij
  have i3 : IntegrableOn (fun x : XN N => fg2b ℓ (wPairC ℓ (g2 v h)) Φ i j x)
      (abox N ℓ) volume :=
    integrableOn_fg2b_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hij
  have i4 : IntegrableOn (fun x : XN N => fg2c ℓ (wPairC ℓ (g0 v h)) Φ i j x)
      (abox N ℓ) volume :=
    integrableOn_fg2c_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hij
  have i5 : IntegrableOn (fun x : XN N => fg3 ℓ (wPairC ℓ (g0 v h)) Φ i j x)
      (abox N ℓ) volume :=
    integrableOn_fg3_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hij
  have i6 : IntegrableOn (fun x : XN N => fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ i j x)
      (abox N ℓ) volume :=
    integrableOn_fg4_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hij
  have i7 : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ j i x)
      (abox N ℓ) volume :=
    integrableOn_fg0_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hij.symm
  have i8 : IntegrableOn (fun x : XN N => fg1 ℓ (wPairC ℓ (g2 v h)) Φ j i x)
      (abox N ℓ) volume :=
    integrableOn_fg1_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hij.symm
  have i9 : IntegrableOn (fun x : XN N => fg2a ℓ (wPairC ℓ (g2 v h)) Φ j i x)
      (abox N ℓ) volume :=
    integrableOn_fg2a_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hij.symm
  have i10 : IntegrableOn (fun x : XN N => fg2b ℓ (wPairC ℓ (g2 v h)) Φ j i x)
      (abox N ℓ) volume :=
    integrableOn_fg2b_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hij.symm
  have i11 : IntegrableOn (fun x : XN N => fg2c ℓ (wPairC ℓ (g0 v h)) Φ j i x)
      (abox N ℓ) volume :=
    integrableOn_fg2c_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hij.symm
  have i12 : IntegrableOn (fun x : XN N => fg3 ℓ (wPairC ℓ (g0 v h)) Φ j i x)
      (abox N ℓ) volume :=
    integrableOn_fg3_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hij.symm
  have i13 : IntegrableOn (fun x : XN N => fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ j i x)
      (abox N ℓ) volume :=
    integrableOn_fg4_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hij.symm
  -- partial sums (orientation (i,j))
  have ip1 : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ i j x
      + fg1 ℓ (wPairC ℓ (g2 v h)) Φ i j x) (abox N ℓ) volume := i0.add i1
  have ip2 : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ i j x
      + fg1 ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg2a ℓ (wPairC ℓ (g2 v h)) Φ i j x)
      (abox N ℓ) volume := ip1.add i2
  have ip3 : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ i j x
      + fg1 ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg2a ℓ (wPairC ℓ (g2 v h)) Φ i j x
      + fg2b ℓ (wPairC ℓ (g2 v h)) Φ i j x) (abox N ℓ) volume := ip2.add i3
  have ip4 : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ i j x
      + fg1 ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg2a ℓ (wPairC ℓ (g2 v h)) Φ i j x
      + fg2b ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg2c ℓ (wPairC ℓ (g0 v h)) Φ i j x)
      (abox N ℓ) volume := ip3.add i4
  have ip5 : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ i j x
      + fg1 ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg2a ℓ (wPairC ℓ (g2 v h)) Φ i j x
      + fg2b ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg2c ℓ (wPairC ℓ (g0 v h)) Φ i j x
      + fg3 ℓ (wPairC ℓ (g0 v h)) Φ i j x) (abox N ℓ) volume := ip4.add i5
  have ip6 : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ i j x
      + fg1 ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg2a ℓ (wPairC ℓ (g2 v h)) Φ i j x
      + fg2b ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg2c ℓ (wPairC ℓ (g0 v h)) Φ i j x
      + fg3 ℓ (wPairC ℓ (g0 v h)) Φ i j x + fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ i j x)
      (abox N ℓ) volume := ip5.add i6
  -- partial sums (orientation (j,i))
  have iq1 : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ j i x
      + fg1 ℓ (wPairC ℓ (g2 v h)) Φ j i x) (abox N ℓ) volume := i7.add i8
  have iq2 : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ j i x
      + fg1 ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg2a ℓ (wPairC ℓ (g2 v h)) Φ j i x)
      (abox N ℓ) volume := iq1.add i9
  have iq3 : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ j i x
      + fg1 ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg2a ℓ (wPairC ℓ (g2 v h)) Φ j i x
      + fg2b ℓ (wPairC ℓ (g2 v h)) Φ j i x) (abox N ℓ) volume := iq2.add i10
  have iq4 : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ j i x
      + fg1 ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg2a ℓ (wPairC ℓ (g2 v h)) Φ j i x
      + fg2b ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg2c ℓ (wPairC ℓ (g0 v h)) Φ j i x)
      (abox N ℓ) volume := iq3.add i11
  have iq5 : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ j i x
      + fg1 ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg2a ℓ (wPairC ℓ (g2 v h)) Φ j i x
      + fg2b ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg2c ℓ (wPairC ℓ (g0 v h)) Φ j i x
      + fg3 ℓ (wPairC ℓ (g0 v h)) Φ j i x) (abox N ℓ) volume := iq4.add i12
  have iq6 : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ j i x
      + fg1 ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg2a ℓ (wPairC ℓ (g2 v h)) Φ j i x
      + fg2b ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg2c ℓ (wPairC ℓ (g0 v h)) Φ j i x
      + fg3 ℓ (wPairC ℓ (g0 v h)) Φ j i x + fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ j i x)
      (abox N ℓ) volume := iq5.add i13
  -- reassemble the two orientations of `pairInts`
  have hA : pairInts ℓ (wPairC ℓ v) (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h))
        (omC (Classical.choose h)) Φ i j
      = (∫ x in abox N ℓ, fg0 ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg1 ℓ (wPairC ℓ (g2 v h)) Φ i j x
        + fg2a ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg2b ℓ (wPairC ℓ (g2 v h)) Φ i j x
        + fg2c ℓ (wPairC ℓ (g0 v h)) Φ i j x + fg3 ℓ (wPairC ℓ (g0 v h)) Φ i j x
        + fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ i j x) := by
    unfold pairInts
    rw [← integral_add i0 i1]
    rw [← integral_add ip1 i2]
    rw [← integral_add ip2 i3]
    rw [← integral_add ip3 i4]
    rw [← integral_add ip4 i5]
    rw [← integral_add ip5 i6]
  have hB : pairInts ℓ (wPairC ℓ v) (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h))
        (omC (Classical.choose h)) Φ j i
      = (∫ x in abox N ℓ, fg0 ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg1 ℓ (wPairC ℓ (g2 v h)) Φ j i x
        + fg2a ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg2b ℓ (wPairC ℓ (g2 v h)) Φ j i x
        + fg2c ℓ (wPairC ℓ (g0 v h)) Φ j i x + fg3 ℓ (wPairC ℓ (g0 v h)) Φ j i x
        + fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ j i x) := by
    unfold pairInts
    rw [← integral_add i7 i8]
    rw [← integral_add iq1 i9]
    rw [← integral_add iq2 i10]
    rw [← integral_add iq3 i11]
    rw [← integral_add iq4 i12]
    rw [← integral_add iq5 i13]
  have iA : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ i j x
      + fg1 ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg2a ℓ (wPairC ℓ (g2 v h)) Φ i j x
      + fg2b ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg2c ℓ (wPairC ℓ (g0 v h)) Φ i j x
      + fg3 ℓ (wPairC ℓ (g0 v h)) Φ i j x + fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ i j x)
      (abox N ℓ) volume := ip6
  have iB : IntegrableOn (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ j i x
      + fg1 ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg2a ℓ (wPairC ℓ (g2 v h)) Φ j i x
      + fg2b ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg2c ℓ (wPairC ℓ (g0 v h)) Φ j i x
      + fg3 ℓ (wPairC ℓ (g0 v h)) Φ j i x + fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ j i x)
      (abox N ℓ) volume := iq6
  have hkey : (fun x : XN N => fg0 ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg1 ℓ (wPairC ℓ (g2 v h)) Φ i j x
        + fg2a ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg2b ℓ (wPairC ℓ (g2 v h)) Φ i j x
        + fg2c ℓ (wPairC ℓ (g0 v h)) Φ i j x + fg3 ℓ (wPairC ℓ (g0 v h)) Φ i j x
        + fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ i j x
        + (fg0 ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg1 ℓ (wPairC ℓ (g2 v h)) Φ j i x
          + fg2a ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg2b ℓ (wPairC ℓ (g2 v h)) Φ j i x
          + fg2c ℓ (wPairC ℓ (g0 v h)) Φ j i x + fg3 ℓ (wPairC ℓ (g0 v h)) Φ j i x
          + fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ j i x))
      = fun x : XN N => (Φ x) ^ 2 * wPairC ℓ v (x i) (x j) := by
    funext x
    have h1 := chosen_pair_pointwise hℓ hvrad h hΦc hij x
    unfold fgsum at h1
    rw [← h1]
    ring
  calc
    pairInts ℓ (wPairC ℓ v) (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h))
        (omC (Classical.choose h)) Φ i j
      + pairInts ℓ (wPairC ℓ v) (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h))
        (omC (Classical.choose h)) Φ j i
        = (∫ x in abox N ℓ, fg0 ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg1 ℓ (wPairC ℓ (g2 v h)) Φ i j x
          + fg2a ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg2b ℓ (wPairC ℓ (g2 v h)) Φ i j x
          + fg2c ℓ (wPairC ℓ (g0 v h)) Φ i j x + fg3 ℓ (wPairC ℓ (g0 v h)) Φ i j x
          + fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ i j x)
        + (∫ x in abox N ℓ, fg0 ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg1 ℓ (wPairC ℓ (g2 v h)) Φ j i x
          + fg2a ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg2b ℓ (wPairC ℓ (g2 v h)) Φ j i x
          + fg2c ℓ (wPairC ℓ (g0 v h)) Φ j i x + fg3 ℓ (wPairC ℓ (g0 v h)) Φ j i x
          + fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ j i x) := by
          rw [hA, hB]
    _ = (∫ x in abox N ℓ, fg0 ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg1 ℓ (wPairC ℓ (g2 v h)) Φ i j x
          + fg2a ℓ (wPairC ℓ (g2 v h)) Φ i j x + fg2b ℓ (wPairC ℓ (g2 v h)) Φ i j x
          + fg2c ℓ (wPairC ℓ (g0 v h)) Φ i j x + fg3 ℓ (wPairC ℓ (g0 v h)) Φ i j x
          + fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ i j x
          + (fg0 ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg1 ℓ (wPairC ℓ (g2 v h)) Φ j i x
            + fg2a ℓ (wPairC ℓ (g2 v h)) Φ j i x + fg2b ℓ (wPairC ℓ (g2 v h)) Φ j i x
            + fg2c ℓ (wPairC ℓ (g0 v h)) Φ j i x + fg3 ℓ (wPairC ℓ (g0 v h)) Φ j i x
            + fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ j i x)) := by
          rw [← integral_add iA iB]
    _ = (∫ x in abox N ℓ, (Φ x) ^ 2 * wPairC ℓ v (x i) (x j)) := by
          rw [hkey]


/-- Per-slot μ identity for the chosen kernel `w₁ := wPair(ℓ,g₀)`: the fibre is
bounded and a.e.-measurable, and the slot factors are continuous on the box. -/
lemma mu_chosen_agree_aux {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) {i : Fin N} :
    muP ℓ (wPairC ℓ (g0 v h)) Φ i + muQP ℓ (wPairC ℓ (g0 v h)) Φ i
      + muQP ℓ (wPairC ℓ (g0 v h)) Φ i + muQ ℓ (wPairC ℓ (g0 v h)) Φ i
    = muPhi ℓ (wPairC ℓ (g0 v h)) Φ i := by
  let F : ℝ³ → ℝ := fun z => ∫ y in acube ℓ, wPair ℓ (g0 v h) z y
  let C : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  have hCb : ∀ z ∈ acube ℓ, |F z| ≤ C := by
    intro z hz
    simpa [F, C] using w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
  have hFaem : AEStronglyMeasurable F (volume.restrict (acube ℓ)) := by
    exact fibre_acube_aem (h := g0 v h) (g0_integrable hR hv_supp h)
  let f : XN N → ℝ := fun x => F (x i)
  have hPc : Continuous (aP ℓ i Φ) := aP_continuous hℓ i hΦc
  have hQc : Continuous (aQ ℓ i Φ) := aQ_continuous hℓ i hΦc
  have hS0c : Continuous (fun x : XN N => (aP ℓ i Φ x) ^ 2) := by fun_prop
  have hS1c : Continuous (fun x : XN N => (aQ ℓ i Φ x) * (aP ℓ i Φ x)) := by fun_prop
  have hS2c : Continuous (fun x : XN N => (aQ ℓ i Φ x) ^ 2) := by fun_prop
  have hS3c : Continuous (fun x : XN N => (Φ x) ^ 2) := by fun_prop
  have i0 : IntegrableOn (fun x : XN N => (aP ℓ i Φ x) ^ 2 * f x) (abox N ℓ) volume := by
    simpa [f] using integrableOn_slot_fibre hℓ i hFaem hCb hS0c
  have i1 : IntegrableOn (fun x : XN N => (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x)
      (abox N ℓ) volume := by
    simpa [f] using integrableOn_slot_fibre hℓ i hFaem hCb hS1c
  have i2 : IntegrableOn (fun x : XN N => (aQ ℓ i Φ x) ^ 2 * f x) (abox N ℓ) volume := by
    simpa [f] using integrableOn_slot_fibre hℓ i hFaem hCb hS2c
  have i3 : IntegrableOn (fun x : XN N => (Φ x) ^ 2 * f x) (abox N ℓ) volume := by
    simpa [f] using integrableOn_slot_fibre hℓ i hFaem hCb hS3c
  have is1 : IntegrableOn (fun x : XN N => (aP ℓ i Φ x) ^ 2 * f x
      + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x) (abox N ℓ) volume := i0.add i1
  have is2 : IntegrableOn (fun x : XN N => (aP ℓ i Φ x) ^ 2 * f x
      + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x
      + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x) (abox N ℓ) volume := is1.add i1
  have hpoint : (fun x : XN N => (aP ℓ i Φ x) ^ 2 * f x
      + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x
      + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x + (aQ ℓ i Φ x) ^ 2 * f x)
      = fun x : XN N => (Φ x) ^ 2 * f x := by
    funext x
    have hlin : aP ℓ i Φ x + aQ ℓ i Φ x = Φ x := by
      unfold aQ
      ring
    have hb : (aP ℓ i Φ x) ^ 2 + 2 * (aQ ℓ i Φ x) * (aP ℓ i Φ x) + (aQ ℓ i Φ x) ^ 2 = (Φ x) ^ 2 := by
      rw [← hlin]
      ring
    calc
      (aP ℓ i Φ x) ^ 2 * f x + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x
          + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x + (aQ ℓ i Φ x) ^ 2 * f x
          = ((aP ℓ i Φ x) ^ 2 + 2 * (aQ ℓ i Φ x) * (aP ℓ i Φ x) + (aQ ℓ i Φ x) ^ 2) * f x := by
            ring
      _ = (Φ x) ^ 2 * f x := by rw [hb]
  calc
    muP ℓ (wPairC ℓ (g0 v h)) Φ i + muQP ℓ (wPairC ℓ (g0 v h)) Φ i
        + muQP ℓ (wPairC ℓ (g0 v h)) Φ i + muQ ℓ (wPairC ℓ (g0 v h)) Φ i
        = (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f x)
            + (∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x)
            + (∫ x in abox N ℓ, (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x)
            + (∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * f x) := by
          unfold muP muQP muQ
          simp [f, F, w1Fibre, wPairC]
    _ = (∫ x in abox N ℓ, (aP ℓ i Φ x) ^ 2 * f x
          + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x
          + (aQ ℓ i Φ x) * (aP ℓ i Φ x) * f x
          + (aQ ℓ i Φ x) ^ 2 * f x) := by
          rw [← integral_add i0 i1]
          rw [← integral_add is1 i1]
          rw [← integral_add is2 i2]
    _ = muPhi ℓ (wPairC ℓ (g0 v h)) Φ i := by
          have hI := congrArg (fun T : XN N → ℝ => ∫ x in abox N ℓ, T x) hpoint
          rw [hI]
          unfold muPhi
          simp [f, F, w1Fibre, wPairC]

/-- Chosen-branch μ-slot-sum identity: `ΣᵢmuP + 2ΣᵢmuQP + ΣᵢmuQ = ΣᵢmuPhi`
for `w₁ := wPair(ℓ,g₀)`. -/
theorem chosen_mu_agree {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (∑ i : Fin N, muP ℓ (wPairC ℓ (g0 v h)) Φ i)
      + 2 * (∑ i : Fin N, muQP ℓ (wPairC ℓ (g0 v h)) Φ i)
      + (∑ i : Fin N, muQ ℓ (wPairC ℓ (g0 v h)) Φ i)
    = ∑ i : Fin N, muPhi ℓ (wPairC ℓ (g0 v h)) Φ i := by
  have hper (i : Fin N) :
      muP ℓ (wPairC ℓ (g0 v h)) Φ i + muQP ℓ (wPairC ℓ (g0 v h)) Φ i
        + muQP ℓ (wPairC ℓ (g0 v h)) Φ i + muQ ℓ (wPairC ℓ (g0 v h)) Φ i
      = muPhi ℓ (wPairC ℓ (g0 v h)) Φ i :=
    mu_chosen_agree_aux hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc (i := i)
  calc
    (∑ i : Fin N, muP ℓ (wPairC ℓ (g0 v h)) Φ i)
      + 2 * (∑ i : Fin N, muQP ℓ (wPairC ℓ (g0 v h)) Φ i)
      + (∑ i : Fin N, muQ ℓ (wPairC ℓ (g0 v h)) Φ i)
        = (∑ i : Fin N, muP ℓ (wPairC ℓ (g0 v h)) Φ i)
            + (∑ i : Fin N, 2 * muQP ℓ (wPairC ℓ (g0 v h)) Φ i)
            + (∑ i : Fin N, muQ ℓ (wPairC ℓ (g0 v h)) Φ i) := by
          rw [Finset.mul_sum]
    _ = ∑ i : Fin N, ((muP ℓ (wPairC ℓ (g0 v h)) Φ i
            + 2 * muQP ℓ (wPairC ℓ (g0 v h)) Φ i) + muQ ℓ (wPairC ℓ (g0 v h)) Φ i) := by
          rw [← Finset.sum_add_distrib]
          rw [← Finset.sum_add_distrib]
    _ = ∑ i : Fin N, muPhi ℓ (wPairC ℓ (g0 v h)) Φ i := by
          apply Finset.sum_congr rfl
          intro i hi
          have h := hper i
          rw [← h]
          ring


/-! ## Pair-part sum (algebraic, no continuity needed) -/

/-- `pairrawSum` equals the sum of the `pairInts` (pure algebra: each word's
pair-summand integral carries its word coefficient already; no integrability
hypotheses are needed because the Bochner integral is linear in constant
factors and `∫`-`Σ` reassociation is formal). -/
lemma pairrawSum_eq_noCont {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (w w1 w2 om : ℝ³ → ℝ³ → ℝ) (Φ : XN N → ℝ) :
    pairrawSum ℓ w w1 w2 om Φ = ∑ p ∈ pairSet N, pairInts ℓ w w1 w2 om Φ p.1 p.2 := by
  unfold pairrawSum
  unfold pairInts
  have h0 : (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, fg0 ℓ w2 Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (1 / 2 : ℝ) (fun x : XN N => (aP ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 * w2 (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold fg0
    ring
  have h1 : 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, fg1 ℓ w2 Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (2 : ℝ) (fun x : XN N => (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.1 (aP ℓ p.2 Φ) x) * w2 (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold fg1
    ring
  have h2a : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, fg2a ℓ w2 Φ p.1 p.2 x) := by
    apply Finset.sum_congr rfl
    intro p hp
    rfl
  have h2b : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) * w2 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, fg2b ℓ w2 Φ p.1 p.2 x) := by
    apply Finset.sum_congr rfl
    intro p hp
    rfl
  have h2c : (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * w1 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, fg2c ℓ w1 Φ p.1 p.2 x) := by
    apply Finset.sum_congr rfl
    intro p hp
    rfl
  have h3 : 2 * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * w1 (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, fg3 ℓ w1 Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (2 : ℝ) (fun x : XN N => (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) * w1 (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold fg3
    ring
  have h4 : (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (q4B ℓ om Φ p x) ^ 2 * w (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, fg4 ℓ w om Φ p.1 p.2 x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← integral_const_mul (1 / 2 : ℝ) (fun x : XN N => (q4B ℓ om Φ p x) ^ 2 * w (x p.1) (x p.2))]
    apply integral_congr_ae
    filter_upwards with x
    unfold fg4
    ring
  rw [h0, h1, h2a, h2b, h2c, h3, h4]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]

/-- The corpus-native potential splitting with the CHOSEN kernels (FS
`lem:potsplit eq:potsplit` at the `L¹` level). -/
theorem potsplit_chosen {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (μ : ℝ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ =
      q0word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q1word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ
        + q3word (N := N) ℓ (wPairC ℓ (g0 v h)) Φ
        + q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
  let w : ℝ³ → ℝ³ → ℝ := wPairC ℓ v
  let w1 : ℝ³ → ℝ³ → ℝ := wPairC ℓ (g0 v h)
  let w2 : ℝ³ → ℝ³ → ℝ := wPairC ℓ (g2 v h)
  let om : ℝ³ → ℝ³ → ℝ := omC (Classical.choose h)
  -- the `w₁`-fibre (bounded and a.e.-measurable; numerator `g₀`)
  let F : ℝ³ → ℝ := fun z => ∫ y in acube ℓ, wPair ℓ (g0 v h) z y
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  have hCb : ∀ z ∈ acube ℓ, |F z| ≤ C0 := by
    intro z hz
    simpa [F, C0] using w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
  have hFaem : AEStronglyMeasurable F (volume.restrict (acube ℓ)) := by
    exact fibre_acube_aem (h := g0 v h) (g0_integrable hR hv_supp h)
  have hSΦc : Continuous (fun x : XN N => (Φ x) ^ 2) := by fun_prop
  -- per-slot integrability of the LHS μ summands: `Φ²·fibre(xᵢ)`
  have hfi (i : Fin N) :
      IntegrableOn (fun x : XN N => (Φ x) ^ 2 * w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
        (abox N ℓ) volume := by
    have hif : IntegrableOn (fun x : XN N => (Φ x) ^ 2 * F (x i)) (abox N ℓ) volume :=
      integrableOn_slot_fibre hℓ i hFaem hCb hSΦc
    simpa [F, w1Fibre, wPairC] using hif
  -- per-pair integrability of the LHS pair summands: `Φ²·w(x_p1,x_p2)`
  have hWi : ∀ p ∈ pairSet N,
      IntegrableOn (fun x : XN N => (Φ x) ^ 2 * w (x p.1) (x p.2)) (abox N ℓ) volume := by
    intro p hp
    have hpne : p.1 ≠ p.2 := by simpa [pairSet] using hp
    have hif : IntegrableOn (fun x : XN N => (Φ x) ^ 2 * wPair ℓ v (x p.1) (x p.2))
        (abox N ℓ) volume :=
      integrableOn_slot_wPair (h := v) hℓ (v_integrable hv_memL1)
        (fun z hz => v_eq_zero_of_norm_ge hv_supp hz) hRℓ hpne hSΦc
    simpa [w, wPairC] using hif
  -- the μ part of the LHS: pull the slot sum out of the integral
  have hmu : (∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) =
      - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i) := by
    calc
      (∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))))
          = (∫ x in abox N ℓ, (- μ) * ((Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = - μ * (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i))) := by
            rw [← integral_const_mul (- μ) (fun x : XN N => (Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))]
      _ = - μ * (∑ i : Fin N, (∫ x in abox N ℓ, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i))) := by
            congr 1
            calc
              (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))
                  = ∫ x in abox N ℓ, (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)) := by
                    apply integral_congr_ae
                    filter_upwards with x
                    rw [Finset.mul_sum]
              _ = ∑ i : Fin N, (∫ x in abox N ℓ, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)) := by
                    exact integral_finsetSum (Finset.univ : Finset (Fin N)) (fun i hi => by simpa [IntegrableOn] using hfi i)
      _ = - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i) := by
            simp [muPhi]
  -- the pair part of the LHS: pull the `pairSet`-sum out of the integral
  have hpair : (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) =
      (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
    calc
      (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2))))
          = (∫ x in abox N ℓ, (1 / 2) * ((Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = (1 / 2) * (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2))) := by
            rw [← integral_const_mul (1 / 2 : ℝ) (fun x : XN N => (Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))]
      _ = (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
            congr 1
            calc
              (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))
                  = ∫ x in abox N ℓ, (∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
                    apply integral_congr_ae
                    filter_upwards with x
                    rw [Finset.mul_sum]
              _ = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
                    exact integral_finsetSum (pairSet N) (fun p hp => by simpa [IntegrableOn] using hWi p hp)
  -- integrability of the two LHS summands (for the single split below)
  have hint1 : IntegrableOn (fun x : XN N =>
      (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) (abox N ℓ) volume := by
    have hfs : IntegrableOn (fun x : XN N => (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)))
        (abox N ℓ) volume := by
      change Integrable (fun x : XN N => ∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i))
          (volume.restrict (abox N ℓ))
      simpa using (integrable_finsetSum (Finset.univ : Finset (Fin N))
        (f := fun (i : Fin N) (x : XN N) => (Φ x) ^ 2 * w1Fibre ℓ w1 (x i))
        (fun i hi => by simpa [IntegrableOn] using hfi i))
    have hpt : (fun x : XN N => (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) =ᵐ[volume.restrict (abox N ℓ)]
        fun x : XN N => (- μ) * (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)) := by
      apply ae_of_all
      intro x
      calc
        (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))
            = (- μ) * ((Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i))) := by ring
        _ = (- μ) * (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)) := by
              rw [Finset.mul_sum]
    have hfsm : Integrable (fun x : XN N => (- μ) * (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)))
        (volume.restrict (abox N ℓ)) := by
      simpa [IntegrableOn] using hfs.const_mul (-μ)
    change Integrable (fun x : XN N =>
        (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) (volume.restrict (abox N ℓ))
    exact hfsm.congr hpt.symm
  have hint2 : IntegrableOn (fun x : XN N =>
      (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) (abox N ℓ) volume := by
    have hfs : IntegrableOn (fun x : XN N => (∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)))
        (abox N ℓ) volume := by
      change Integrable (fun x : XN N => ∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2))
          (volume.restrict (abox N ℓ))
      simpa using (integrable_finsetSum (pairSet N)
        (f := fun (p : Fin N × Fin N) (x : XN N) => (Φ x) ^ 2 * w (x p.1) (x p.2))
        (fun p hp => by simpa [IntegrableOn] using hWi p hp))
    have hpt : (fun x : XN N => (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) =ᵐ[volume.restrict (abox N ℓ)]
        fun x : XN N => (1 / 2) * (∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
      apply ae_of_all
      intro x
      calc
        (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))
            = (1 / 2) * ((Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2))) := by ring
        _ = (1 / 2) * (∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
              rw [Finset.mul_sum]
    have hfsm : Integrable (fun x : XN N => (1 / 2) * (∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)))
        (volume.restrict (abox N ℓ)) := by
      simpa [IntegrableOn] using hfs.const_mul (1 / 2)
    change Integrable (fun x : XN N =>
        (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) (volume.restrict (abox N ℓ))
    exact hfsm.congr hpt.symm
  -- (i) the LHS is the μ-term plus the pair term
  have hLHS : qLHSword ℓ μ w w1 Φ =
      - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i)
        + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
    calc
      qLHSword ℓ μ w w1 Φ = ∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))
          + (1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2))) := by
            rfl
      _ = (∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))))
          + (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) := by
            rw [← integral_add hint1 hint2]
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i)
          + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
            rw [hmu, hpair]
  -- (ii) the five words: pair parts (the raw seven sums) + μ parts
  have hwords : q0word ℓ μ w1 w2 Φ + q1word ℓ μ w1 w2 Φ + q2word ℓ μ w1 w2 Φ
      + q3word ℓ w1 Φ + q4word ℓ w om Φ
      = pairrawSum ℓ w w1 w2 om Φ
        - μ * ((∑ i : Fin N, muP ℓ w1 Φ i) + 2 * (∑ i : Fin N, muQP ℓ w1 Φ i)
          + (∑ i : Fin N, muQ ℓ w1 Φ i)) := by
    unfold q0word q1word q2word q3word q4word
    simp [muP, muQP, muQ, pairrawSum]
    ring
  -- (iii) the pair-claim: pair sums telescope into half the `Φ²`-sums
  have hpairsum : pairrawSum ℓ w w1 w2 om Φ
      = (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
    calc
      pairrawSum ℓ w w1 w2 om Φ
          = (1 / 2) * (pairrawSum ℓ w w1 w2 om Φ + (∑ p ∈ pairSet N, pairInts ℓ w w1 w2 om Φ p.2 p.1)) := by
            rw [pairrawSum_eq_noCont hℓ w w1 w2 om Φ]
            have hswap : (∑ p ∈ pairSet N, pairInts ℓ w w1 w2 om Φ p.2 p.1)
                = ∑ p ∈ pairSet N, pairInts ℓ w w1 w2 om Φ p.1 p.2 := by
              exact pairSet_swap_sum (fun p : Fin N × Fin N => pairInts ℓ w w1 w2 om Φ p.1 p.2)
            rw [hswap]
            ring
      _ = (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
            congr 1
            rw [pairrawSum_eq_noCont hℓ w w1 w2 om Φ]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro p hp
            have hpne : p.1 ≠ p.2 := by simpa [pairSet] using hp
            exact chosen_pair_agree hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hpne
  -- (iv) μ sums
  have hmusum : (∑ i : Fin N, muP ℓ w1 Φ i) + 2 * (∑ i : Fin N, muQP ℓ w1 Φ i)
      + (∑ i : Fin N, muQ ℓ w1 Φ i) = ∑ i : Fin N, muPhi ℓ w1 Φ i := by
    simpa [w1] using
      (chosen_mu_agree hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc)
  calc
    qLHSword ℓ μ w w1 Φ = - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i)
        + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
          rw [hLHS]
    _ = - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i) + pairrawSum ℓ w w1 w2 om Φ := by
          rw [hpairsum]
    _ = q0word ℓ μ w1 w2 Φ + q1word ℓ μ w1 w2 Φ + q2word ℓ μ w1 w2 Φ
        + q3word ℓ w1 Φ + q4word ℓ w om Φ := by
          rw [hwords]
          rw [← hmusum]
          ring

end BoseGases

end Submission
