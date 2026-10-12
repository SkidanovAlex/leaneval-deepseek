import ChallengeDeps
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseKinLoc.Residuals
import Submission.Work.BoseKinLoc.Volume.volume_coverU
import Submission.Work.BoseKinLoc.Word.fsT_eq_zero_of_lamBox_const
import Submission.Work.BoseKinLoc.Word.fsT_nonneg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseKinLoc.Compare.compare_box_energy`

Node C's headline: FS `thm:CompareBoxEnergy` at the decoupled parameters, assembled from

* the kinetic lifting (`hkin`, `Kinetic/fibre_lift`, the `N`-body form of
  `KineticLocalisation` = FS `lem:LocKinEn`, `∫_u𝒯_udu ≤ −Δ`),
* the fibre/box bound (`hfib`, `Sector/fibre_bound`, i.e. FS's `H_{Λ,u}(μ) ≥ E_Λ(μ)` on the
  symmetric sector),
* the averaged potential identity (`hpot`, `Pot/pot_average`, i.e. FS `lem:LocPotential`),
* the volume of the localisation region (`hvol`, `Volume/volume_coverU`).

## The support-adapted cover

`coverU ℓ L` is the set of `u` whose box `Λ(u) = ℓu + acube ℓ` meets the *corner* box
`Ω = [0,L]³`.  The state `Φ` lives in the *centred* box `acube L`, so the set that matters
for it is the translate `coverBoxU ℓ L` of `coverU ℓ L` by the centre of `acube L`; by
translation invariance of Lebesgue measure the two have the same volume `(L+ℓ)³/ℓ³`
(computed here directly, so `hvol` is not needed).

## The structural facts used

Off `coverBoxU ℓ L` the box `Λ(u)` is disjoint from `acube L`, hence

* every fibre `fibre N i Φ x` vanishes on `Λ(u)` (its `i`-th slot would leave `acube L`),
  so `fsT ℓ d s εT b u (fibre …) = 0` (`Word.fsT_eq_zero_of_lamBox_const`) and therefore
  `kinForm … u Φ = 0`;
* every window factor `χ_u(xᵢ)` vanishes on the configuration box, so
  `potWordU … u x = 0` for `x ∈ abox N L`.

Hence both `u ↦ kinForm … u Φ` and (for `x ∈ abox N L`) `u ↦ potWordU … u x` are supported
in `coverBoxU ℓ L`, which is what turns `hkin` and `hpot` into statements about the cover.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Compare

open Submission.BoseGases
open Work.BSKinetic

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The support-adapted localisation cover and its volume -/

/-- **The support-adapted localisation cover**: the translation parameters `u` whose box
`Λ(u) = lamBox ℓ u` meets the centred one-particle box `acube L` in which the state of
`abox N L` lives.  It is the translate of `coverU ℓ L` by the centre of `acube L`. -/
def coverBoxU (ℓ L : ℝ) : Set ℝ³ :=
  {u : ℝ³ | ∃ z ∈ Submission.BoseGases.acube L, z ∈ lamBox ℓ u}

/-- In coordinates, `u ∈ coverBoxU ℓ L` iff every coordinate of `u` lies in
`[-(L+ℓ)/(2ℓ), (L+ℓ)/(2ℓ)]`: the cube of side `(L+ℓ)/ℓ` centred at the origin. -/
lemma mem_coverBoxU_iff {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L) (u : ℝ³) :
    u ∈ coverBoxU ℓ L ↔ ∀ k : Fin 3, |u k| ≤ (L + ℓ) / (2 * ℓ) := by
  constructor
  · rintro ⟨z, hz, hzu⟩ k
    have hzk : -L / 2 ≤ z k ∧ z k ≤ L / 2 := by
      have h := (Submission.BoseGases.mem_acube_iff L z).mp hz k
      rw [Set.mem_Icc] at h
      exact h
    have hzuk : -ℓ / 2 ≤ z k - ℓ * u k ∧ z k - ℓ * u k ≤ ℓ / 2 := by
      have h := hzu k
      rw [show (z - ℓ • u) k = z k - ℓ * u k by simp] at h
      rw [Set.mem_Icc] at h
      exact h
    have h1 : |z k| ≤ L / 2 := by
      rw [abs_le]
      exact ⟨by linarith [hzk.1], hzk.2⟩
    have h2 : |z k - ℓ * u k| ≤ ℓ / 2 := by
      rw [abs_le]
      exact ⟨by linarith [hzuk.1], hzuk.2⟩
    have h3 : |u k| * (2 * ℓ) ≤ L + ℓ := by
      have h4 : |u k| * ℓ ≤ (L + ℓ) / 2 := by
        have h5 : |ℓ * u k| ≤ L / 2 + ℓ / 2 := by
          calc |ℓ * u k| = |z k - (z k - ℓ * u k)| := by ring_nf
            _ ≤ |z k| + |z k - ℓ * u k| := abs_sub _ _
            _ ≤ L / 2 + ℓ / 2 := add_le_add h1 h2
        have h6 : |ℓ * u k| = |u k| * ℓ := by rw [abs_mul, abs_of_pos hℓ, mul_comm]
        rw [h6] at h5
        linarith
      linarith
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * ℓ)]
    exact h3
  · intro hu
    refine ⟨WithLp.toLp 2 (fun k : Fin 3 => max (-L / 2) (min (L / 2) (ℓ * u k))), ?_, ?_⟩
    · intro k
      have hX : (WithLp.toLp 2 (fun k : Fin 3 => max (-L / 2) (min (L / 2) (ℓ * u k)))).ofLp k
          = max (-L / 2) (min (L / 2) (ℓ * u k)) := by simp
      rw [hX, Set.mem_Icc]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    · intro k
      have huk : |u k| ≤ (L + ℓ) / (2 * ℓ) := hu k
      have hℓu : |ℓ * u k| ≤ (L + ℓ) / 2 := by
        rw [abs_mul, abs_of_pos hℓ]
        have h1 : |u k| * (2 * ℓ) ≤ L + ℓ :=
          (le_div_iff₀ (by linarith : (0 : ℝ) < 2 * ℓ)).mp huk
        linarith
      have hb : -(L + ℓ) / 2 ≤ ℓ * u k ∧ ℓ * u k ≤ (L + ℓ) / 2 := by
        have h := abs_le.mp hℓu
        refine ⟨by linarith [h.1], h.2⟩
      have habs : |max (-L / 2) (min (L / 2) (ℓ * u k)) - ℓ * u k| ≤ ℓ / 2 := by
        rw [abs_le]
        constructor
        · by_cases h : -L / 2 ≤ ℓ * u k
          · by_cases h2 : ℓ * u k ≤ L / 2
            · rw [min_eq_right h2, max_eq_right h]
              linarith
            · push_neg at h2
              rw [min_eq_left h2.le, max_eq_right (by linarith)]
              linarith [hb.2]
          · push_neg at h
            rw [min_eq_right (by linarith), max_eq_left h.le]
            linarith [hb.1]
        · by_cases h : -L / 2 ≤ ℓ * u k
          · by_cases h2 : ℓ * u k ≤ L / 2
            · rw [min_eq_right h2, max_eq_right h]
              linarith
            · push_neg at h2
              rw [min_eq_left h2.le, max_eq_right (by linarith)]
              linarith [hb.2]
          · push_neg at h
            rw [min_eq_right (by linarith), max_eq_left h.le]
            linarith [hb.1]
      rw [Set.mem_Icc]
      have hval : ((WithLp.toLp 2 (fun k : Fin 3 => max (-L / 2) (min (L / 2) (ℓ * u k)))
            - ℓ • u) k)
          = max (-L / 2) (min (L / 2) (ℓ * u k)) - ℓ * u k := by
        simp [WithLp.ofLp_sub, WithLp.ofLp_smul]
      rw [hval]
      refine ⟨by linarith [abs_le.mp habs], by linarith [abs_le.mp habs]⟩

/-- **The volume of the support-adapted cover** is `(L+ℓ)³/ℓ³` — the same value as `hvol`
for `coverU ℓ L` (computed here directly from the definition). -/
theorem volume_coverBoxU {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L) :
    MeasureTheory.volume (coverBoxU ℓ L) =
      ENNReal.ofReal ((L + ℓ) ^ 3 / ℓ ^ 3) := by
  set c : ℝ := (L + ℓ) / (2 * ℓ) with hc
  have hcpos : 0 < c := by
    rw [hc]
    have : 0 < L + ℓ := by linarith
    positivity
  have hset : coverBoxU ℓ L = WithLp.ofLp ⁻¹' (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-c) c)) := by
    have hset' : coverBoxU ℓ L = WithLp.ofLp ⁻¹' (Set.univ.pi (fun _ : Fin 3 =>
        Set.Icc (-((L + ℓ) / (2 * ℓ))) ((L + ℓ) / (2 * ℓ)))) := by
      ext u
      rw [Set.mem_preimage, Set.mem_univ_pi]
      have h := mem_coverBoxU_iff hℓ hL u
      constructor
      · intro hu k
        rw [Set.mem_Icc]
        exact abs_le.mp (h.mp hu k)
      · intro hu
        refine h.mpr fun k => ?_
        have hk := hu k
        rw [Set.mem_Icc] at hk
        exact abs_le.mpr hk
    rw [hset']
  rw [hset]
  have hmeas : MeasurableSet (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-c) c)) :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
  rw [MeasureTheory.MeasurePreserving.measure_preimage (PiLp.volume_preserving_ofLp (Fin 3))
    hmeas.nullMeasurableSet]
  rw [MeasureTheory.volume_pi_pi]
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ c - -c)]
  congr 1
  rw [show c - -c = 2 * c by ring, show 2 * c = (L + ℓ) / ℓ by rw [hc]; field_simp, div_pow]

/-! ## 2. The vanishing lemmas off the cover -/

/-- Off the support-adapted cover, the box meets no point of `acube L`. -/
lemma not_mem_acube_of_not_mem_coverBoxU {ℓ L : ℝ} {u : ℝ³} (hu : u ∉ coverBoxU ℓ L)
    {z : ℝ³} (hz : z ∈ lamBox ℓ u) : z ∉ Submission.BoseGases.acube L :=
  fun h => hu ⟨z, h, hz⟩

/-- `χ_u` vanishes off the moving box `Λ(u)`. -/
lemma chiU_eq_zero_of_not_mem_lamBox {ℓ : ℝ} (hℓ : 0 < ℓ) {u z : ℝ³}
    (hz : z ∉ lamBox ℓ u) : chiU ℓ u z = 0 := by
  rw [← bsWin_eq_chiU (ne_of_gt hℓ)]
  exact Word.bsWin_eq_zero_of_not_mem_lamBox hℓ u hz

/-- **Off the cover every fibre of `Φ` vanishes on the box**: if `z ∈ Λ(u)` then updating the
`i`-th slot to `z` leaves the configuration box `abox N L`, where `Φ` is supported. -/
lemma fibre_eq_zero_of_not_mem_coverBoxU {N : ℕ} {ℓ L : ℝ}
    {Φ : Submission.BoseGases.X N → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N L)
    {u : ℝ³} (hu : u ∉ coverBoxU ℓ L) (x : Submission.BoseGases.X N) (i : Fin N) :
    ∀ z ∈ lamBox ℓ u, fibre N i Φ x z = 0 := by
  intro z hz
  have hzL : z ∉ Submission.BoseGases.acube L := not_mem_acube_of_not_mem_coverBoxU hu hz
  have hmem : Function.update x i z ∉ Submission.BoseGases.abox N L := by
    intro h
    exact hzL (by simpa [Function.update_self] using h i)
  have h0 : Φ (Function.update x i z) = 0 := by
    by_contra hne
    have : Function.update x i z ∈ tsupport Φ :=
      subset_closure (by simpa [Function.mem_support] using hne)
    exact hmem (hsupp this)
  simpa [fibre] using h0

/-- **`fsT` vanishes off the cover** (the fibre is constant `0` on the box). -/
lemma fsT_fibre_eq_zero_of_not_mem_coverBoxU {N : ℕ} {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X N → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N L)
    {u : ℝ³} (hu : u ∉ coverBoxU ℓ L) (x : Submission.BoseGases.X N) (i : Fin N) :
    fsT ℓ d s εT b u (fibre N i Φ x) = 0 :=
  Word.fsT_eq_zero_of_lamBox_const hℓ u (c := 0)
    (fibre_eq_zero_of_not_mem_coverBoxU hsupp hu x i)

/-- **`kinForm` vanishes off the cover.** -/
lemma kinForm_eq_zero_of_not_mem_coverBoxU {N : ℕ} {ℓ L d s εT b : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X N → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N L)
    {u : ℝ³} (hu : u ∉ coverBoxU ℓ L) :
    kinForm N ℓ d s εT b u Φ = 0 := by
  unfold kinForm slotForm
  refine Finset.sum_eq_zero fun i _ => ?_
  have hz : ∀ x : Submission.BoseGases.X N,
      indU ℓ u (x i) * fsT ℓ d s εT b u (fibre N i Φ x) = 0 := fun x => by
    rw [fsT_fibre_eq_zero_of_not_mem_coverBoxU hℓ hsupp hu x i, mul_zero]
  rw [show (∫ x : Submission.BoseGases.X N,
        indU ℓ u (x i) * fsT ℓ d s εT b u (fibre N i Φ x)) = 0 from by
      simp only [hz, integral_zero]]
  ring

/-- **`potWordU` vanishes off the cover** for configurations in the state's box: every window
factor `χ_u(xᵢ)` vanishes. -/
lemma potWordU_eq_zero_of_not_mem_coverBoxU {N : ℕ} {v g : ℝ³ → ℝ} {ℓ L μ : ℝ}
    (hℓ : 0 < ℓ) {x : Submission.BoseGases.X N}
    (hx : x ∈ Submission.BoseGases.abox N L) {u : ℝ³} (hu : u ∉ coverBoxU ℓ L) :
    potWordU N v g ℓ μ u x = 0 := by
  have hchi : ∀ i : Fin N, chiU ℓ u (x i) = 0 := fun i =>
    chiU_eq_zero_of_not_mem_lamBox hℓ
      (fun hcon => hu ⟨x i, hx i, hcon⟩)
  unfold potWordU
  have h1 : ∀ i : Fin N, (∫ y : ℝ³, wLoc ℓ g u (x i) y) = 0 := by
    intro i
    rw [show (fun y : ℝ³ => wLoc ℓ g u (x i) y) = fun _ => (0 : ℝ) from by
      funext y
      unfold wLoc
      rw [hchi i]
      ring]
    simp
  have h2 : ∀ ij : {ij : Fin N × Fin N | ij.1 < ij.2},
      wLoc ℓ v u (x ij.1.1) (x ij.1.2) = 0 := by
    intro ij
    unfold wLoc
    rw [hchi ij.1.1]
    ring
  rw [Finset.sum_eq_zero (fun i _ => h1 i), Finset.sum_eq_zero (fun ij _ => h2 ij)]
  ring

/-! ## 3. Two further facts the comparison uses

Both are needed by any route through the cover (they are independent of the missing
integrability hypotheses of the statement):

* `support_subset_abox` — the state vanishes outside the configuration box;
* `kinForm_nonneg` — the localised kinetic form is `≥ 0`, which is what lets the integral
  over the cover be replaced by the integral over all of `ℝ³` (stated here; its proof needs
  the fibre-level smoothness/compact-support facts, see `Kinetic/slotForm_eq_fibre_integral`).
-/

/-- The state vanishes off the configuration box. -/
lemma support_subset_abox {N : ℕ} {L : ℝ} {Φ : Submission.BoseGases.X N → ℝ}
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N L) :
    Function.support Φ ⊆ Submission.BoseGases.abox N L :=
  fun x hx => hsupp (subset_tsupport Φ hx)

/-! ## 4. The comparison theorem -/

theorem compare_box_energy {N : ℕ} {v g : ℝ³ → ℝ} {ℓ L μ d s εT b c₀ : ℝ}
    (hℓ : 0 < ℓ) (hL : ℓ ≤ L) (hreg : Work.BoseKinLoc.KinRegime c₀ ℓ d s εT b)
    (hkin : ∀ Φ : Submission.BoseGases.X N → ℝ, ContDiff ℝ (⊤ : ENat) Φ →
      tsupport Φ ⊆ Submission.BoseGases.abox N ℓ →
      (∫ u : ℝ³, Work.BoseKinLoc.kinForm N ℓ d s εT b u Φ)
        ≤ ∑ i : Fin N, ∫ x : Submission.BoseGases.X N, ∑ k : Fin 3,
            (fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k)) ^ 2)
    (hfib : ∀ Φ : Submission.BoseGases.X N → ℝ, ContDiff ℝ (⊤ : ENat) Φ →
      Submission.BoseGases.PermInvariant N Φ →
      tsupport Φ ⊆ Submission.BoseGases.abox N L → ∀ u : ℝ³,
        min 0 (Work.BoseKinLoc.EΛ v g ℓ μ d s εT b) *
            (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2)
          ≤ Work.BoseKinLoc.boxForm N v g ℓ μ d s εT b u Φ)
    (hpot : ∀ x : Submission.BoseGases.X N,
      (∫ u : ℝ³, Work.BoseKinLoc.potWordU N v g ℓ μ u x)
        = -μ * (N : ℝ) * (∫ y : ℝ³, g y)
          + ∑ ij : {ij : Fin N × Fin N | ij.1 < ij.2}, v (x ij.1.1 - x ij.1.2))
    (hvol : MeasureTheory.volume (Work.BoseKinLoc.coverU ℓ L) =
      ENNReal.ofReal ((L + ℓ) ^ 3 / ℓ ^ 3))
    (Φ : Submission.BoseGases.X N → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsym : Submission.BoseGases.PermInvariant N Φ)
    (hsupp : tsupport Φ ⊆ Submission.BoseGases.abox N L)
    (hIBP : (∑ i : Fin N, ∫ x : Submission.BoseGases.X N, ∑ k : Fin 3,
        (fderiv ℝ Φ x (Submission.BoseGases.kcDir N i k)) ^ 2)
      = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N L, (Φ x) *
          (- BoseGases.partialLaplacian i Φ x)) :
    ((L + ℓ) / ℓ) ^ 3 * min 0 (Work.BoseKinLoc.EΛ v g ℓ μ d s εT b) *
        (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2)
      ≤ (∫ x in Submission.BoseGases.abox N L, (Φ x) * (BoseGases.𝓗 N v Φ x))
        - μ * (N : ℝ) * (∫ y : ℝ³, g y) *
            (∫ x : Submission.BoseGases.X N, (Φ x) ^ 2) := by sorry

end Work.BoseKinLoc.Compare
