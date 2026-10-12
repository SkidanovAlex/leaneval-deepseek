import ChallengeDeps
import Submission.PotChosen
import Submission.Work.SmallBoxSuperadd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Chosen-branch integrability of the `qLHSword` diagonal density

The `qLHSword`-density pieces (one-body fibre terms `Φ(x)²·w1Fibre(w1)(xᵢ)`
and pair terms `Φ(x)²·wPair(xᵢ,xⱼ)`) are integrable over the centred box in
the chosen branch (the χ-renormalized kernels with numerator `v` / `g₀`,
`v` merely `L¹`): the pair terms via
`PotChosen.integrableOn_slot_wPair` (WordInteg bounded-mul), the one-body
fibre terms via `PotChosen.integrableOn_slot_fibre` with the a.e.-
measurability `PotChosen.fibre_acube_aem` and the fibre bound
`PotChosen.w1c_fibre_acube_abs_le`.

Headline: `chosen_qLHSden_integrableOn` — for every `N`, scale `s`, smooth
`Φ`, the full diagonal density product `Φ²·qLHSden N s μ w w1` (with
`w := wPairC s v`, `w1 := wPairC s (g0 v h)`) is integrable over
`abox N s`.  This discharges the `hD`-type hypotheses of
`SboxESlice.sboxE_ge_sboxE1_add_sboxE2` and the `qLHSword` slice identities.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

section ChosenBranch

/- Standing chosen-branch hypotheses: `(hℓ : 0 < ℓ)`, `(μ : ℝ)`,
`(hv_nonneg : 0 ≤ v)`, `(hvrad : IsRadial v)`, `(hv_memL1 : MemLp v 1)`,
`(hR : 0 < R)`, `(hv_supp : tsupport v ⊆ ball 0 R)`,
`(h : ∃ w, IsRadial w ∧ IsScatteringSolution w v)`,
`(hRℓ : R ≤ ℓ * chiR0)`, `{Φ} (hΦc : Continuous Φ)`. -/

/-- Pair atom: `Φ²·wPair(ℓ,h)(xᵢ,xⱼ)` is integrable over the box
(`h := v` or `h := g0`, support-bounded numerators). -/
lemma chosen_pair_atom_integrableOn {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (_hR : 0 < R)
    {h : ℝ³ → ℝ} (hh : Integrable h) (hzero : ∀ z : ℝ³, R ≤ ‖z‖ → h z = 0)
    (hRℓ : R ≤ ℓ * chiR0) {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X N => (Φ x) ^ 2 * wPairC ℓ h (x i) (x j)) (abox N ℓ) volume := by
  simpa [wPairC, mul_comm] using
    (integrableOn_slot_wPair (h := h) hℓ hh hzero hRℓ hij (hΦc.pow 2))

/-- One-body fibre atom: `Φ²·w1Fibre(ℓ,wPair(ℓ,h))(xᵢ)` is integrable over
the box (numerator `h := g0`, fibre bounded on the cube). -/
lemma chosen_fibre_atom_integrableOn {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (_hR : 0 < R)
    {h : ℝ³ → ℝ} (hh : Integrable h) (_hRℓ : R ≤ ℓ * chiR0)
    {C : ℝ} (hC : ∀ z ∈ acube ℓ, |∫ y in acube ℓ, wPair ℓ h z y| ≤ C)
    (i : Fin N) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X N => (Φ x) ^ 2 *
        w1Fibre ℓ (wPairC ℓ h) (x i)) (abox N ℓ) volume := by
  have hfac := fibre_acube_aem (ℓ := ℓ) (h := h) hh
  have hF : AEStronglyMeasurable (fun z : ℝ³ => w1Fibre ℓ (wPairC ℓ h) z)
      (volume.restrict (acube ℓ)) := by
    simpa [w1Fibre, wPairC] using hfac
  simpa [mul_comm] using
    (integrableOn_slot_fibre (N := N) (ℓ := ℓ) hℓ i hF hC (hΦc.pow 2))

/-- Chosen-branch: the `g₀`-fibre is bounded on the centred cube (the form
`chosen_fibre_atom_integrableOn` needs). -/
lemma chosen_g0_fibre_bounded {v : ℝ³ → ℝ} {R ℓ : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * chiR0) :
    ∀ z ∈ acube ℓ, |∫ y in acube ℓ, wPair ℓ (g0 v h) z y| ≤ chiSup ^ 2 * 2 * (8 * π * a v) := by
  intro z hz
  exact w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z

/-- Chosen-branch pair atom with numerator `v`. -/
lemma chosen_v_pair_integrableOn {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    {v : ℝ³ → ℝ} (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hRℓ : R ≤ ℓ * chiR0)
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X N => (Φ x) ^ 2 * wPairC ℓ v (x i) (x j)) (abox N ℓ) volume := by
  exact chosen_pair_atom_integrableOn (N := N) hℓ hR (h := v) (v_integrable hv_memL1)
    (fun z hz => v_eq_zero_of_norm_ge hv_supp hz) hRℓ hij hΦc

/-- Chosen-branch pair atom with numerator `g₀`. -/
lemma chosen_g0_pair_integrableOn {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    {v : ℝ³ → ℝ} (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X N => (Φ x) ^ 2 * wPairC ℓ (g0 v h) (x i) (x j)) (abox N ℓ) volume := by
  exact chosen_pair_atom_integrableOn (N := N) hℓ hR (h := g0 v h) (g0_integrable hR hv_supp h)
    (fun z hz => g0_zero_of_norm_ge hv_supp hz h) hRℓ hij hΦc

/-- Chosen-branch one-body atom (`w₁ := wPair(g₀)`). -/
lemma chosen_g0_fibre_atom_integrableOn {N : ℕ} {ℓ R : ℝ} (hℓ : 0 < ℓ) (hR : 0 < R)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i : Fin N) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X N => (Φ x) ^ 2 *
        w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i)) (abox N ℓ) volume := by
  exact chosen_fibre_atom_integrableOn (N := N) hℓ hR (h := g0 v h) (g0_integrable hR hv_supp h)
    hRℓ (chosen_g0_fibre_bounded hR hv_nonneg hvrad hv_supp h hℓ hRℓ) i hΦc

end ChosenBranch


/-! ## Density-level integrability (the `hD`-discharge) -/

/-- Pointwise algebra: `a·qLHSden(...)` splits into the fibre-sum and
pair-sum pieces (used to prove the integrability of the density product). -/
lemma sq_mul_qLHSden_split (N : ℕ) (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ) (a : ℝ) (x : X N) :
    a * qLHSden N s μ w w1 x
      = - μ * (∑ i : Fin N, a * w1Fibre s w1 (x i))
          + (1 / 2 : ℝ) * (∑ p ∈ pairSet N, a * w (x p.1) (x p.2)) := by
  rw [qLHSden]
  rw [mul_add]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  ring

/-- The full `qLHSword` diagonal density product `Φ²·qLHSden N s μ w w1` with
the chosen kernels `w := wPairC s v`, `w1 := wPairC s (g0 v h)` is integrable
over `abox N s`. -/
lemma chosen_qLHSden_integrableOn {N : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ}
    (hs : 0 < s) (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_memL1 : MemLp v 1) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R ≤ s * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X N => (Φ x) ^ 2 *
        qLHSden N s μ (wPairC s v) (wPairC s (g0 v h)) x) (abox N s) volume := by
  let w : ℝ³ → ℝ³ → ℝ := wPairC s v
  let w1 : ℝ³ → ℝ³ → ℝ := wPairC s (g0 v h)
  have hFibre (i : Fin N) : IntegrableOn (fun x : X N => (Φ x) ^ 2 *
      w1Fibre s w1 (x i)) (abox N s) volume := by
    exact chosen_g0_fibre_atom_integrableOn (N := N) hs hR hv_nonneg hvrad hv_supp h hRs i hΦc
  have hPair (p : Fin N × Fin N) (hp : p ∈ pairSet N) : IntegrableOn (fun x : X N =>
      (Φ x) ^ 2 * w (x p.1) (x p.2)) (abox N s) volume := by
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    exact chosen_v_pair_integrableOn (N := N) hs hR hv_memL1 hv_supp hRs hij hΦc
  have hFibreSum : IntegrableOn (fun x : X N => ∑ i : Fin N, (Φ x) ^ 2 * w1Fibre s w1 (x i))
      (abox N s) volume := by
    change Integrable (fun x : X N => ∑ i : Fin N, (Φ x) ^ 2 * w1Fibre s w1 (x i))
        (volume.restrict (abox N s))
    exact integrable_finsetSum Finset.univ (fun i _ => hFibre i)
  have hPairSum : IntegrableOn (fun x : X N =>
      ∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)) (abox N s) volume := by
    change Integrable (fun x : X N => ∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2))
        (volume.restrict (abox N s))
    exact integrable_finsetSum (pairSet N) (fun p hp => hPair p hp)
  have hEq : (fun x : X N => (Φ x) ^ 2 * qLHSden N s μ w w1 x)
      = fun x : X N => - μ * (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre s w1 (x i))
          + (1 / 2 : ℝ) * (∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
    funext x
    exact sq_mul_qLHSden_split N s μ w w1 ((Φ x) ^ 2) x
  rw [hEq]
  exact (hFibreSum.const_mul (-μ)).add (hPairSum.const_mul (1 / 2 : ℝ))

/-- Pointwise algebra for the block-1 density (embedded coordinates). -/
lemma sq_mul_qLHSden1_split {N1 N2 : ℕ} (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ)
    (a : ℝ) (x : X (N1+N2)) :
    a * qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x
      = - μ * (∑ i : Fin N1, a * w1Fibre s w1 (x (Fin.castAdd N2 i)))
          + (1 / 2 : ℝ) * (∑ p ∈ pairSet N1,
              a * w (x (Fin.castAdd N2 p.1)) (x (Fin.castAdd N2 p.2))) := by
  rw [qLHSden1]
  rw [mul_add]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  ring

/-- Chosen-branch: the block-1 density product is integrable over the merged
centred box. -/
lemma chosen_qLHSden1_integrableOn {N1 N2 : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ}
    (hs : 0 < s) (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_memL1 : MemLp v 1) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R ≤ s * chiR0) {Φ : X (N1+N2) → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2 *
        qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x)
      (abox (N1+N2) s) volume := by
  let w : ℝ³ → ℝ³ → ℝ := wPairC s v
  let w1 : ℝ³ → ℝ³ → ℝ := wPairC s (g0 v h)
  have hFibre (i : Fin N1) : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2 *
      w1Fibre s w1 (x (Fin.castAdd N2 i))) (abox (N1+N2) s) volume := by
    exact chosen_g0_fibre_atom_integrableOn (N := N1+N2) hs hR hv_nonneg hvrad hv_supp h hRs
      (Fin.castAdd N2 i) hΦc
  have hPair (p : Fin N1 × Fin N1) (hp : p ∈ pairSet N1) : IntegrableOn
      (fun x : X (N1+N2) => (Φ x) ^ 2 * w (x (Fin.castAdd N2 p.1)) (x (Fin.castAdd N2 p.2)))
      (abox (N1+N2) s) volume := by
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hij' : Fin.castAdd N2 p.1 ≠ Fin.castAdd N2 p.2 := by
      intro h
      exact hij ((Fin.castAdd_inj).mp h)
    exact chosen_v_pair_integrableOn (N := N1+N2) hs hR hv_memL1 hv_supp hRs hij' hΦc
  have hFibreSum : IntegrableOn (fun x : X (N1+N2) =>
      ∑ i : Fin N1, (Φ x) ^ 2 * w1Fibre s w1 (x (Fin.castAdd N2 i)))
      (abox (N1+N2) s) volume := by
    change Integrable (fun x : X (N1+N2) =>
        ∑ i : Fin N1, (Φ x) ^ 2 * w1Fibre s w1 (x (Fin.castAdd N2 i)))
        (volume.restrict (abox (N1+N2) s))
    exact integrable_finsetSum Finset.univ (fun i _ => hFibre i)
  have hPairSum : IntegrableOn (fun x : X (N1+N2) =>
      ∑ p ∈ pairSet N1, (Φ x) ^ 2 * w (x (Fin.castAdd N2 p.1)) (x (Fin.castAdd N2 p.2)))
      (abox (N1+N2) s) volume := by
    change Integrable (fun x : X (N1+N2) =>
        ∑ p ∈ pairSet N1, (Φ x) ^ 2 * w (x (Fin.castAdd N2 p.1)) (x (Fin.castAdd N2 p.2)))
        (volume.restrict (abox (N1+N2) s))
    exact integrable_finsetSum (pairSet N1) (fun p hp => hPair p hp)
  have hEq : (fun x : X (N1+N2) => (Φ x) ^ 2 *
        qLHSden1 (N1 := N1) (N2 := N2) s μ w w1 x)
      = fun x : X (N1+N2) => - μ * (∑ i : Fin N1,
            (Φ x) ^ 2 * w1Fibre s w1 (x (Fin.castAdd N2 i)))
          + (1 / 2 : ℝ) * (∑ p ∈ pairSet N1,
              (Φ x) ^ 2 * w (x (Fin.castAdd N2 p.1)) (x (Fin.castAdd N2 p.2))) := by
    funext x
    exact sq_mul_qLHSden1_split (N1 := N1) (N2 := N2) s μ w w1 ((Φ x) ^ 2) x
  rw [hEq]
  exact (hFibreSum.const_mul (-μ)).add (hPairSum.const_mul (1 / 2 : ℝ))

/-- Pointwise algebra for the block-2 density (embedded coordinates). -/
lemma sq_mul_qLHSden2_split {N1 N2 : ℕ} (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ)
    (a : ℝ) (x : X (N1+N2)) :
    a * qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x
      = - μ * (∑ j : Fin N2, a * w1Fibre s w1 (x (Fin.natAdd N1 j)))
          + (1 / 2 : ℝ) * (∑ p ∈ pairSet N2,
              a * w (x (Fin.natAdd N1 p.1)) (x (Fin.natAdd N1 p.2))) := by
  rw [qLHSden2]
  rw [mul_add]
  rw [← Finset.mul_sum]
  rw [← Finset.mul_sum]
  ring

/-- Chosen-branch: the block-2 density product is integrable over the merged
centred box. -/
lemma chosen_qLHSden2_integrableOn {N1 N2 : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ}
    (hs : 0 < s) (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_memL1 : MemLp v 1) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRs : R ≤ s * chiR0) {Φ : X (N1+N2) → ℝ} (hΦc : Continuous Φ) :
    IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2 *
        qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x)
      (abox (N1+N2) s) volume := by
  let w : ℝ³ → ℝ³ → ℝ := wPairC s v
  let w1 : ℝ³ → ℝ³ → ℝ := wPairC s (g0 v h)
  have hFibre (j : Fin N2) : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2 *
      w1Fibre s w1 (x (Fin.natAdd N1 j))) (abox (N1+N2) s) volume := by
    exact chosen_g0_fibre_atom_integrableOn (N := N1+N2) hs hR hv_nonneg hvrad hv_supp h hRs
      (Fin.natAdd N1 j) hΦc
  have hPair (p : Fin N2 × Fin N2) (hp : p ∈ pairSet N2) : IntegrableOn
      (fun x : X (N1+N2) => (Φ x) ^ 2 * w (x (Fin.natAdd N1 p.1)) (x (Fin.natAdd N1 p.2)))
      (abox (N1+N2) s) volume := by
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    have hij' : Fin.natAdd N1 p.1 ≠ Fin.natAdd N1 p.2 := by
      intro h
      exact hij ((Fin.natAdd_inj N1).mp h)
    exact chosen_v_pair_integrableOn (N := N1+N2) hs hR hv_memL1 hv_supp hRs hij' hΦc
  have hFibreSum : IntegrableOn (fun x : X (N1+N2) =>
      ∑ j : Fin N2, (Φ x) ^ 2 * w1Fibre s w1 (x (Fin.natAdd N1 j)))
      (abox (N1+N2) s) volume := by
    change Integrable (fun x : X (N1+N2) =>
        ∑ j : Fin N2, (Φ x) ^ 2 * w1Fibre s w1 (x (Fin.natAdd N1 j)))
        (volume.restrict (abox (N1+N2) s))
    exact integrable_finsetSum Finset.univ (fun j _ => hFibre j)
  have hPairSum : IntegrableOn (fun x : X (N1+N2) =>
      ∑ p ∈ pairSet N2, (Φ x) ^ 2 * w (x (Fin.natAdd N1 p.1)) (x (Fin.natAdd N1 p.2)))
      (abox (N1+N2) s) volume := by
    change Integrable (fun x : X (N1+N2) =>
        ∑ p ∈ pairSet N2, (Φ x) ^ 2 * w (x (Fin.natAdd N1 p.1)) (x (Fin.natAdd N1 p.2)))
        (volume.restrict (abox (N1+N2) s))
    exact integrable_finsetSum (pairSet N2) (fun p hp => hPair p hp)
  have hEq : (fun x : X (N1+N2) => (Φ x) ^ 2 *
        qLHSden2 (N1 := N1) (N2 := N2) s μ w w1 x)
      = fun x : X (N1+N2) => - μ * (∑ j : Fin N2,
            (Φ x) ^ 2 * w1Fibre s w1 (x (Fin.natAdd N1 j)))
          + (1 / 2 : ℝ) * (∑ p ∈ pairSet N2,
              (Φ x) ^ 2 * w (x (Fin.natAdd N1 p.1)) (x (Fin.natAdd N1 p.2))) := by
    funext x
    exact sq_mul_qLHSden2_split (N1 := N1) (N2 := N2) s μ w w1 ((Φ x) ^ 2) x
  rw [hEq]
  exact (hFibreSum.const_mul (-μ)).add (hPairSum.const_mul (1 / 2 : ℝ))

end BoseGases
