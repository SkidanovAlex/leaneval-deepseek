import Mathlib
import Submission.Work.EKLRelCross.bigShape_flowers
import Submission.Work.EKLRelCross.local_flower

/-!
# `Work.EKLRelCross.bigShape_flowers_fr`

Flowers of `U`-plaques exist, with the bases covering the free set **pointwise** (Pisa 6.13–6.15):

for a horospherical `U ≤ SL₃(ℝ)`, a probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved
by the diagonal element `α^{t₀}` and contracting `U`, and any `R > 0`, there are countably many
plaque algebras `(Z n, m n)` with Borel bases `G n ⊆ Z n` such that

* every point with free `U`-orbit lies in some `G n`, and
* at every `x ∈ G n` the whole `R`-plaque `(V R ∩ U) • x` of the point lies in the atom
  `atom (m n) x` of the plaque algebra.

This is the pointwise-cover refinement of `Work.EKLRelCross.bigShape_flowers` (which only
records that `⋃ n, G n` is conull).

## Route

* `Work.EKLRelCross.free_orbits_of_contracting` gives a.e. freeness of the `U`-orbits; since
  freeness is equivalent to injectivity of the orbit map `u ↦ u • x`, the *injective* locus `S`
  is conull, hence nonempty (this is the only place where `μ` enters the proof).
* `Work.EKLRelCross.local_flower` (Pisa 6.7 + 6.9–6.15) gives, through **every** point `x₀` of
  `S`, an open `O ∋ x₀`, a Borel `G ⊆ Z` with `x₀ ∈ G`, a plaque algebra `(Z, m)`, and the two
  properties
  `O ∩ free ⊆ G` and `V R ∩ U ⊆ shape m U x` for all `x ∈ G`.
* A countable basis `(basis n)` of `X₃` (from `P_X3` via `secondCountableTopology_X3`) turns the
  uncountable family of local flowers into a countable one: for each `n` select a point `s n ∈ S`
  with `basis n ⊆ O_{s n}` whenever such a point exists, and an arbitrary point of `S` otherwise.
  The corresponding pair `(Z_{s n}, m_{s n}, G_{s n})` is then a valid flower for every `n`.
* Covering: if `y` has free orbit then `y ∈ S`; pick a basis element `basis n ∋ y` contained in
  `O ⟨y, ·⟩`; then `basis n ⊆ O_{s n}`, so `y ∈ O_{s n} ∩ free ⊆ G_{s n}`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- Freeness of the `U`-orbit of `x` is the same as injectivity of the orbit map `u ↦ u • x`. -/
lemma bigShape_fr_free_orbit_injective {U : Subgroup SL3} {x : X3}
    (h : ∀ u ∈ U, u • x = x → u = 1) :
    ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂ := by
  intro u₁ h₁ u₂ h₂ heq
  have hfix : (u₂⁻¹ * u₁) • x = x := by rw [mul_smul, heq, inv_smul_smul]
  have h1 : u₂⁻¹ * u₁ = 1 := h _ (U.mul_mem (U.inv_mem h₂) h₁) hfix
  calc u₁ = u₂ * (u₂⁻¹ * u₁) := (mul_inv_cancel_left u₂ u₁).symm
    _ = u₂ := by rw [h1, mul_one]

theorem bigShape_flowers_fr (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ] (U : Subgroup Work.EKLContract.SL3)
    (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (R : ℝ) (hR : 0 < R) :
    ∃ (Z G : ℕ → Set Work.EKLContract.X3) (m : ℕ → MeasurableSpace Work.EKLContract.X3),
      (∀ n, Work.EKLContract.IsPlaqueAlgebra U (Z n) (m n)) ∧
      (∀ n, MeasurableSet (G n) ∧ G n ⊆ Z n) ∧
      ({x : Work.EKLContract.X3 | ∀ u ∈ U, u • x = x → u = 1} ⊆ ⋃ n, G n) ∧
      (∀ n, ∀ x ∈ G n, ∀ u ∈ (Work.EKLContract.V R ∩ (U : Set Work.EKLContract.SL3)), u • x ∈ Work.EKLContract.atom (m n) x) := by
  classical
  -- a.e. freeness of the `U`-orbits
  have hfree_ae : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 :=
    free_orbits_of_contracting h2 hU t0 ht0 hcontr
  -- the locus of points with injective orbit map
  set S : Set X3 := {x | ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x = u₂ • x → u₁ = u₂} with hSdef
  have hSae : ∀ᵐ x ∂μ, x ∈ S := by
    filter_upwards [hfree_ae] with x hx
    exact bigShape_fr_free_orbit_injective hx
  -- `S` is nonempty
  have hSne : S.Nonempty := by
    by_contra h
    have hSe : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h0 : μ Sᶜ = 0 := MeasureTheory.ae_iff.mp hSae
    rw [hSe, Set.compl_empty, MeasureTheory.measure_univ] at h0
    exact one_ne_zero h0
  -- a local flower through every point of `S`
  have hloc : ∀ x : S, ∃ (Z : Set X3) (m : MeasurableSpace X3) (G O : Set X3),
      IsOpen O ∧ (x : X3) ∈ O ∧
      @MeasurableSet X3 Work.EKLContract.instMeasurableSpaceX3 G ∧ G ⊆ Z ∧ IsPlaqueAlgebra U Z m ∧
      (x : X3) ∈ G ∧ O ∩ {y | ∀ u ∈ U, u • y = y → u = 1} ⊆ G ∧
      ∀ y ∈ G, V R ∩ (U : Set SL3) ⊆ shape m U y :=
    fun x => local_flower h2 hU (x : X3) x.property R hR
  choose Zfun mfun Gfun Ofun hOopen hxO hGmeas hGsub hplaq hxG hOG hshape using hloc
  -- a countable basis of `X₃`
  haveI : SecondCountableTopology X3 := secondCountableTopology_X3 h2
  obtain ⟨basis, hbas⟩ := TopologicalSpace.exists_seq_basis X3
  -- the selected point of `S` for each basis element
  obtain ⟨x₀, hx₀⟩ := hSne
  let s : ℕ → S := fun n =>
    if h : ∃ x : S, basis n ⊆ Ofun x then Classical.choose h else ⟨x₀, hx₀⟩
  have hs_spec : ∀ n, (∃ x : S, basis n ⊆ Ofun x) → basis n ⊆ Ofun (s n) := by
    intro n h
    have hsn : s n = Classical.choose h := by simp only [s]; exact dif_pos h
    rw [hsn]
    exact Classical.choose_spec h
  refine ⟨fun n => Zfun (s n), fun n => Gfun (s n), fun n => mfun (s n), ?_, ?_, ?_, ?_⟩
  · -- each member is a plaque algebra
    intro n
    exact hplaq (s n)
  · -- the bases are Borel and contained in the plaque algebras
    intro n
    exact ⟨hGmeas (s n), hGsub (s n)⟩
  · -- the bases cover the free set pointwise
    intro y hy
    have hyS : y ∈ S := bigShape_fr_free_orbit_injective hy
    have hyO : y ∈ Ofun ⟨y, hyS⟩ := hxO ⟨y, hyS⟩
    obtain ⟨t, ht, hyt, hts⟩ := hbas.exists_subset_of_mem_open hyO (hOopen ⟨y, hyS⟩)
    obtain ⟨n, rfl⟩ := ht
    have hex : ∃ x : S, basis n ⊆ Ofun x := ⟨⟨y, hyS⟩, hts⟩
    have hyOf : y ∈ Ofun (s n) := hs_spec n hex hyt
    exact Set.mem_iUnion.mpr ⟨n, hOG (s n) ⟨hyOf, hy⟩⟩
  · -- the `R`-plaque of a base point lies in the atom
    intro n x hx u hu
    exact (hshape (s n) x hx hu).2

end Work.EKLRelCross
