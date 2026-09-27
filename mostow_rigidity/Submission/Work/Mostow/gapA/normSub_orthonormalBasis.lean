import Mathlib
import Submission.Work.Mostow.gapA.axisNormDefs
import Submission.Work.Mostow.perpNullUnit
import Submission.Work.Mostow.gapA.geodFacts

/-!
# Orthonormal basis of the normal plane `NormSub a b`

For two distinct boundary points `a ≠ b` of `Sph 3`, the normal plane
`NormSub a b = {Z | ⟨Z,θ_a⟩ = ⟨Z,θ_b⟩ = 0}` of the geodesic `geodSet a b` is a
**two-dimensional positive definite** subspace of Minkowski space `ℝ^{3,1}`, and together with
the two null vectors `θ_a`, `θ_b` it spans the whole space.

This file constructs a positive definite orthonormal basis of `NormSub a b` (Gram–Schmidt in
one step: take one unit vector `W` of the plane, and normalise any nonzero vector of the kernel
of the functional `Z ↦ ⟨Z,W⟩` on it), and records the two spanning statements.

* `nsb_mem_ker_perpMap_iff` : `NormSub a b` is the kernel of `Z ↦ (⟨Z,θ_a⟩,⟨Z,θ_b⟩)`;
* `nsb_perpMap_surjective`  : that map is onto `ℝ × ℝ` (so the kernel has dimension `4 - 2 = 2`);
* `nsb_finrank_NormSub`     : `finrank ℝ (NormSub a b) = 2`;
* `normSub_orthonormalBasis`: existence of the orthonormal basis with both spanning statements.
-/

namespace Work.Mostow.gapA

set_option maxHeartbeats 1000000

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open _root_.Matrix

noncomputable section

variable {a b : E 3}

/-! ## The normal plane as the kernel of the pair of pairings -/

lemma nsb_mem_ker_perpMap_iff (Z : Fin 3 ⊕ Fin 1 → ℝ) :
    Z ∈ LinearMap.ker (perpMap a b) ↔ Z ∈ NormSub a b := by
  rw [mem_NormSub, LinearMap.mem_ker]
  constructor
  · intro h
    constructor
    · rw [mink_eq_mform]
      exact (congrArg Prod.fst h).trans (by simp)
    · rw [mink_eq_mform]
      exact (congrArg Prod.snd h).trans (by simp)
  · rintro ⟨h1, h2⟩
    have h1' : mform Z (theta a) = 0 := by rw [← mink_eq_mform]; exact h1
    have h2' : mform Z (theta b) = 0 := by rw [← mink_eq_mform]; exact h2
    show (mform Z (theta a), mform Z (theta b)) = (0 : ℝ × ℝ)
    rw [h1', h2']
    rfl

/-! ## The two-pairing map is onto -/

lemma nsb_perpMap_surjective (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) :
    (perpMap a b).range = ⊤ := by
  rw [LinearMap.range_eq_top]
  rintro ⟨r, s⟩
  set D : ℝ := mink (nvec a) (nvec b) with hD
  have hDne : D ≠ 0 := by rw [hD]; exact mink_nvec_pair_ne_zero ha hb hab
  have hba : mink (nvec b) (nvec a) = D := by rw [hD, minkSeg_comm]
  have hselfa : mink (nvec a) (nvec a) = 0 := mink_nvec_self' ha
  have hselfb : mink (nvec b) (nvec b) = 0 := mink_nvec_self' hb
  refine ⟨(s / mink (nvec b) (nvec a)) • nvec a + (r / D) • nvec b, ?_⟩
  have hZ1 : mink ((s / mink (nvec b) (nvec a)) • nvec a + (r / D) • nvec b) (nvec a) = r := by
    rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', hselfa, hba, mul_zero, zero_add,
      div_mul_cancel₀ r hDne]
  have hZ2 : mink ((s / mink (nvec b) (nvec a)) • nvec a + (r / D) • nvec b) (nvec b) = s := by
    rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', hba, hselfb, hD, mul_zero, add_zero,
      div_mul_cancel₀ s hDne]
  refine Prod.ext ?_ ?_
  · show mform ((s / mink (nvec b) (nvec a)) • nvec a + (r / D) • nvec b) (theta a) = r
    rw [← mink_eq_mform, ← nvec_eq_theta]
    exact hZ1
  · show mform ((s / mink (nvec b) (nvec a)) • nvec a + (r / D) • nvec b) (theta b) = s
    rw [← mink_eq_mform, ← nvec_eq_theta]
    exact hZ2

/-! ## The normal plane has dimension `2` -/

lemma nsb_finrank_NormSub (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) :
    Module.finrank ℝ (NormSub a b) = 2 := by
  have hsurj := nsb_perpMap_surjective (a := a) (b := b) ha hb hab
  have hrk := LinearMap.finrank_range_add_finrank_ker (perpMap a b)
  rw [hsurj, finrank_top] at hrk
  simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_sum, Fintype.card_fin, Fintype.card_unique] at hrk
  have hker : NormSub a b = LinearMap.ker (perpMap a b) := by
    ext Z; rw [nsb_mem_ker_perpMap_iff]
  rw [hker]
  omega

/-! ## The orthonormal basis -/

theorem normSub_orthonormalBasis (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3)
    (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b) :
    ∃ E1 E2 : Fin 3 ⊕ Fin 1 → ℝ,
      E1 ∈ Work.Mostow.gapA.NormSub a b ∧ E2 ∈ Work.Mostow.gapA.NormSub a b ∧
      Work.Mostow.mink E1 E1 = 1 ∧ Work.Mostow.mink E2 E2 = 1 ∧ Work.Mostow.mink E1 E2 = 0 ∧
      (∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ Work.Mostow.gapA.NormSub a b →
        Z = Work.Mostow.mink Z E1 • E1 + Work.Mostow.mink Z E2 • E2) ∧
      (∀ Z : Fin 3 ⊕ Fin 1 → ℝ, ∃ α β γ δ : ℝ,
        Z = α • Work.Mostow.nvec a + β • Work.Mostow.nvec b + γ • E1 + δ • E2) := by
  obtain ⟨W, hWa, hWb, hWW⟩ := perpNullUnit (n := 3) (by norm_num) ha hb hab
  have hWmem : W ∈ NormSub a b := by
    rw [mem_NormSub]
    exact ⟨by rw [mink_eq_mform]; exact hWa, by rw [mink_eq_mform]; exact hWb⟩
  have hWnorm : mink W W = 1 := by rw [mink_eq_mform]; exact hWW
  -- a second direction in the plane, orthogonal to `W`
  let f : NormSub a b →ₗ[ℝ] ℝ :=
    { toFun := fun Z => mink (Z : Fin 3 ⊕ Fin 1 → ℝ) W
      map_add' := fun x y => by
        show mink ((x : Fin 3 ⊕ Fin 1 → ℝ) + (y : Fin 3 ⊕ Fin 1 → ℝ)) W
            = mink (x : Fin 3 ⊕ Fin 1 → ℝ) W + mink (y : Fin 3 ⊕ Fin 1 → ℝ) W
        rw [minkSeg_add_left]
      map_smul' := fun c x => by
        show mink (c • (x : Fin 3 ⊕ Fin 1 → ℝ)) W = c • mink (x : Fin 3 ⊕ Fin 1 → ℝ) W
        rw [mink_smul_left'', smul_eq_mul] }
  have hfker : LinearMap.ker f ≠ ⊥ := by
    refine LinearMap.ker_ne_bot_of_finrank_lt (f := f) ?_
    rw [nsb_finrank_NormSub ha hb hab]
    simp
  obtain ⟨Z₀, hZ₀mem, hZ₀ne⟩ := (Submodule.ne_bot_iff (LinearMap.ker f)).mp hfker
  have hZ₀vec : (Z₀ : Fin 3 ⊕ Fin 1 → ℝ) ≠ 0 := fun h => hZ₀ne (Subtype.ext h)
  have hZ₀orth : mink (Z₀ : Fin 3 ⊕ Fin 1 → ℝ) W = 0 := (LinearMap.mem_ker).mp hZ₀mem
  have hZ₀pos : 0 < mink (Z₀ : Fin 3 ⊕ Fin 1 → ℝ) Z₀ := by
    rcases lt_or_eq_of_le (mink_nonneg_of_mem_NormSub ha Z₀.2) with h | h
    · exact h
    · exact absurd (eq_zero_of_mem_NormSub_of_mink_self_eq_zero ha hb hab Z₀.2 h.symm) hZ₀vec
  set c : ℝ := (Real.sqrt (mink (Z₀ : Fin 3 ⊕ Fin 1 → ℝ) Z₀))⁻¹ with hcdef
  set E2 : Fin 3 ⊕ Fin 1 → ℝ := c • (Z₀ : Fin 3 ⊕ Fin 1 → ℝ) with hE2def
  have hE2mem : E2 ∈ NormSub a b := (NormSub a b).smul_mem c Z₀.2
  have hc2 : c * c = (mink (Z₀ : Fin 3 ⊕ Fin 1 → ℝ) Z₀)⁻¹ := by
    rw [hcdef, ← mul_inv, ← sq, Real.sq_sqrt (le_of_lt hZ₀pos)]
  have hE2norm : mink E2 E2 = 1 := by
    rw [hE2def, mink_smul_left'', mink_smul_right'', ← mul_assoc, hc2,
      inv_mul_cancel₀ (ne_of_gt hZ₀pos)]
  have hE2orth : mink E2 W = 0 := by
    rw [hE2def, mink_smul_left'', hZ₀orth, mul_zero]
  have hWE2 : mink W E2 = 0 := by rw [minkSeg_comm]; exact hE2orth
  -- `W` and `E2` are orthonormal and span the plane
  have hind : LinearIndependent ℝ
      ![(⟨W, hWmem⟩ : NormSub a b), (⟨E2, hE2mem⟩ : NormSub a b)] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum : g 0 • (⟨W, hWmem⟩ : NormSub a b) + g 1 • (⟨E2, hE2mem⟩ : NormSub a b) = 0 := by
      have h := hg
      rwa [Fin.sum_univ_two] at h
    have hcoe : g 0 • W + g 1 • E2 = 0 := by
      have h := congrArg (fun x : NormSub a b => (x : Fin 3 ⊕ Fin 1 → ℝ)) hsum
      simpa using h
    have h1 : g 0 = 0 := by
      have hpair : mink (g 0 • W + g 1 • E2) W = 0 := by rw [hcoe]; simp [mink]
      rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', hWnorm, hE2orth, mul_one,
        mul_zero, add_zero] at hpair
      exact hpair
    have h2 : g 1 = 0 := by
      have hpair : mink (g 0 • W + g 1 • E2) E2 = 0 := by rw [hcoe]; simp [mink]
      rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', hWE2, hE2norm, mul_one,
        mul_zero, zero_add] at hpair
      exact hpair
    fin_cases i
    · exact h1
    · exact h2
  have hspan : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b → ∃ α β : ℝ, Z = α • W + β • E2 := by
    intro Z hZ
    have htop : Submodule.span ℝ (Set.range ![(⟨W, hWmem⟩ : NormSub a b),
        (⟨E2, hE2mem⟩ : NormSub a b)]) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card hind, nsb_finrank_NormSub ha hb hab]
      simp
    have hmem : (⟨Z, hZ⟩ : NormSub a b) ∈ Submodule.span ℝ (Set.range
        ![(⟨W, hWmem⟩ : NormSub a b), (⟨E2, hE2mem⟩ : NormSub a b)]) := by
      rw [htop]; trivial
    have hrange : Set.range ![(⟨W, hWmem⟩ : NormSub a b), (⟨E2, hE2mem⟩ : NormSub a b)]
        = ({(⟨W, hWmem⟩ : NormSub a b), (⟨E2, hE2mem⟩ : NormSub a b)} : Set (NormSub a b)) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ rfl
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
    rw [hrange, Submodule.mem_span_pair] at hmem
    obtain ⟨α, β, hαβ⟩ := hmem
    refine ⟨α, β, ?_⟩
    have h := congrArg (fun x : NormSub a b => (x : Fin 3 ⊕ Fin 1 → ℝ)) hαβ
    simpa using h.symm
  -- the whole space is spanned
  have hspanV : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, ∃ α β γ δ : ℝ,
      Z = α • nvec a + β • nvec b + γ • W + δ • E2 := by
    intro Z
    set D : ℝ := mink (nvec a) (nvec b) with hDdef
    have hDne : D ≠ 0 := by rw [hDdef]; exact mink_nvec_pair_ne_zero ha hb hab
    have hb_a : mink (nvec b) (nvec a) = D := by rw [hDdef, minkSeg_comm]
    have hNmem : Z - (mink Z (nvec b) / D) • nvec a - (mink Z (nvec a) / D) • nvec b
        ∈ NormSub a b := by
      refine ⟨?_, ?_⟩
      · simp only [mink_sub_left', mink_smul_left'', mink_nvec_self' ha, hb_a, mul_zero,
          sub_zero, div_mul_cancel₀ (mink Z (nvec a)) hDne, sub_self]
      · simp only [mink_sub_left', mink_smul_left'', mink_nvec_self' hb, ← hDdef, mul_zero,
          div_mul_cancel₀ (mink Z (nvec b)) hDne, sub_self]
    obtain ⟨γ, δ, hγδ⟩ := hspan _ hNmem
    refine ⟨mink Z (nvec b) / D, mink Z (nvec a) / D, γ, δ, ?_⟩
    have h : Z = ((mink Z (nvec b) / D) • nvec a + (mink Z (nvec a) / D) • nvec b)
        + (γ • W + δ • E2) := by rw [← hγδ]; abel
    conv_lhs => rw [h]
    abel
  refine ⟨W, E2, hWmem, hE2mem, hWnorm, hE2norm, hWE2, ?_, hspanV⟩
  intro Z hZ
  obtain ⟨α, β, hαβ⟩ := hspan Z hZ
  have h1 : mink Z W = α := by
    conv_lhs => rw [hαβ]
    rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', hWnorm, hE2orth, mul_one,
      mul_zero, add_zero]
  have h2 : mink Z E2 = β := by
    conv_lhs => rw [hαβ]
    rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', hWE2, hE2norm, mul_zero,
      mul_one, zero_add]
  conv_lhs => rw [hαβ]
  rw [h1, h2]

end

end Work.Mostow.gapA
