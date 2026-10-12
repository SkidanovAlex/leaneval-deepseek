import Mathlib
import ChallengeDeps
import Submission.BoxEnergy
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Box-in-box monotonicity of the finite-volume energy.

A trial state of a smaller box is a trial state of every larger box (both with
Dirichlet conditions), and the Rayleigh quotient of the state does not change
when the box is enlarged.  Hence the box energy is non-increasing in the side
length.  This is the monotonicity half of the thermodynamic-limit machinery.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- If `L1 ≤ L2` then `box N L1 ⊆ box N L2`. -/
lemma box_mono {N : ℕ} {L1 L2 : ℝ} (hLL : L1 ≤ L2) : box N L1 ⊆ box N L2 := by
  intro x hx
  rw [mem_box_iff] at hx ⊢
  intro i k
  exact Set.Icc_subset_Icc (le_refl 0) hLL (hx i k)

/-- A `CInfty0Box N L1` function is also a `CInfty0Box N L2` function when `L1 ≤ L2`. -/
def incl {N : ℕ} {L1 L2 : ℝ} (hLL : L1 ≤ L2) (Ψ : CInfty0Box N L1) : CInfty0Box N L2 where
  toFun := Ψ
  contDiff := by
    have hAmb : ContDiff ℝ ∞ (Ψ : X N → ℝ) := psi_contDiff Ψ
    exact hAmb.contDiffOn
  support := by
    exact Ψ.support.trans (interior_mono (box_mono (N := N) hLL))
  nezero := Ψ.nezero

/-! ## States vanish outside the small box, so integrals do not change on enlargement -/

/-- A state `Ψ` of the box of side `L` vanishes outside that box. -/
lemma psi_eq_zero_of_not_mem_box {N : ℕ} {L : ℝ} (Ψ : CInfty0Box N L) {x : X N}
    (hx : x ∉ box N L) : (Ψ : X N → ℝ) x = 0 := by
  exact psi_eq_zero_of_not_mem_interior Ψ (fun hxi => hx (interior_subset hxi))

/-- A function vanishing outside the small box has equal integrals over the large and the
small box (the function vanishes on `box N L2 \ box N L1` as well as on the complement
of `box N L1`, so both set-integrals equal the whole-space integral). -/
lemma integral_box_eq_of_le {N : ℕ} {L1 L2 : ℝ} (hLL : L1 ≤ L2) {g : X N → ℝ}
    (hg : ∀ x, x ∉ box N L1 → g x = 0) :
    (∫ x in box N L2, g x) = ∫ x in box N L1, g x := by
  calc
    (∫ x in box N L2, g x) = ∫ x, g x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero (s := box N L2) (μ := volume)
      intro x hx
      apply hg
      intro hx1
      exact hx (box_mono (N := N) hLL hx1)
    _ = ∫ x in box N L1, g x := by
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := box N L1) (μ := volume) hg).symm

/-- The Rayleigh quotient of a state depends on the box only through the state:
for `Ψ ∈ CInfty0Box N L1` with `0 < L1 ≤ L2` the quotient computed in the box of
side `L2` equals that computed in the box of side `L1`. -/
lemma rayleigh_eq_of_le {N : ℕ} {L1 L2 : ℝ} {v : ℝ³ → ℝ} (hL1 : 0 < L1)
    (hLL : L1 ≤ L2) (Ψ : CInfty0Box N L1) :
    (∫ x in box N L2, Ψ x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) /
        (∫ x in box N L2, (Ψ x) ^ 2)
      = (∫ x in box N L1, Ψ x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) /
        (∫ x in box N L1, (Ψ x) ^ 2) := by
  -- the box is nonempty when `L1 > 0`; `hL1` is kept for the interface
  have _hL1pos := hL1
  have hvan_num : ∀ x : X N, x ∉ box N L1 →
      (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x = 0 := by
    intro x hx
    rw [psi_eq_zero_of_not_mem_box Ψ hx]
    ring
  have hvan_den : ∀ x : X N, x ∉ box N L1 → (Ψ : X N → ℝ) x ^ 2 = 0 := by
    intro x hx
    rw [psi_eq_zero_of_not_mem_box Ψ hx]
    ring
  have hnum : (∫ x in box N L2, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) =
      ∫ x in box N L1, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x := by
    exact integral_box_eq_of_le hLL hvan_num
  have hden : (∫ x in box N L2, (Ψ : X N → ℝ) x ^ 2) = ∫ x in box N L1, (Ψ : X N → ℝ) x ^ 2 := by
    exact integral_box_eq_of_le hLL hvan_den
  rw [hnum, hden]

/-- The same equality with the norm-form denominator `(√ (∫ Ψ²))²` used in the definition
of the box energy. -/
lemma rayleigh_norm_eq_of_le {N : ℕ} {L1 L2 : ℝ} {v : ℝ³ → ℝ} (hL1 : 0 < L1)
    (hLL : L1 ≤ L2) (Ψ : CInfty0Box N L1) :
    (∫ x in box N L2, Ψ x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) /
        (√ (∫ x in box N L2, ((Ψ : X N → ℝ) x) ^ 2)) ^ 2
      = (∫ x in box N L1, Ψ x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) /
        (√ (∫ x in box N L1, ((Ψ : X N → ℝ) x) ^ 2)) ^ 2 := by
  have hpl := rayleigh_eq_of_le (v := v) hL1 hLL Ψ
  have hge2 : 0 ≤ (∫ x in box N L2, ((Ψ : X N → ℝ) x) ^ 2) :=
    integral_nonneg (fun x => sq_nonneg (Ψ x))
  have hge1 : 0 ≤ (∫ x in box N L1, ((Ψ : X N → ℝ) x) ^ 2) :=
    integral_nonneg (fun x => sq_nonneg (Ψ x))
  calc
    (∫ x in box N L2, Ψ x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) /
        (√ (∫ x in box N L2, ((Ψ : X N → ℝ) x) ^ 2)) ^ 2
        = (∫ x in box N L2, Ψ x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) /
            (∫ x in box N L2, ((Ψ : X N → ℝ) x) ^ 2) := by
          rw [Real.sq_sqrt hge2]
    _ = (∫ x in box N L1, Ψ x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) /
            (∫ x in box N L1, ((Ψ : X N → ℝ) x) ^ 2) := hpl
    _ = (∫ x in box N L1, Ψ x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) /
            (√ (∫ x in box N L1, ((Ψ : X N → ℝ) x) ^ 2)) ^ 2 := by
          rw [Real.sq_sqrt hge1]

/-! ## Nonnegativity of the per-state Rayleigh quotient -/

/-- The numerator of the Rayleigh quotient (the expectation of `𝓗`) is nonnegative. -/
lemma boxEnergy_num_nonneg {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (Ψ : CInfty0Box N L) :
    0 ≤ (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) := by
  by_cases hint : IntegrableOn (intIntegrand N L v Ψ) (box N L) volume
  · have hkinInt := integrableOn_kinIntegrand N hL Ψ
    have h1 : (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x)
        = kineticEnergy N L Ψ + interactionEnergy N L v Ψ := by
      calc
        (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x)
            = ∫ x in box N L, (kinIntegrand N L Ψ + intIntegrand N L v Ψ) x := by
              rw [numerator_integrand_eq]
        _ = (∫ x in box N L, kinIntegrand N L Ψ x) + ∫ x in box N L, intIntegrand N L v Ψ x := by
              exact integral_add (μ := volume.restrict (box N L)) hkinInt hint
        _ = kineticEnergy N L Ψ + interactionEnergy N L v Ψ := by
              rw [boxInt_kinIntegrand N hL Ψ, boxInt_intIntegrand N L v Ψ]
    rw [h1]
    exact add_nonneg (kineticEnergy_nonneg hL Ψ) (interactionEnergy_nonneg hv Ψ)
  · have hkinInt := integrableOn_kinIntegrand N hL Ψ
    have hnot : ¬ IntegrableOn (fun x : X N =>
        (kinIntegrand N L Ψ x) + (intIntegrand N L v Ψ x)) (box N L) volume := by
      intro hsum
      apply hint
      -- intIntegrand = (kin + int) - kin pointwise
      have hsub : IntegrableOn (fun x : X N =>
          (kinIntegrand N L Ψ x + intIntegrand N L v Ψ x) - kinIntegrand N L Ψ x)
          (box N L) volume := IntegrableOn.sub hsum hkinInt
      convert hsub using 1
      funext x
      ring
    have hzero : (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) = 0 := by
      calc
        (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x)
            = ∫ x in box N L, (kinIntegrand N L Ψ + intIntegrand N L v Ψ) x := by
              rw [numerator_integrand_eq]
        _ = 0 := by
              exact integral_undef (μ := volume.restrict (box N L)) hnot
    rw [hzero]

/-- The Rayleigh quotient of every admissible state is nonnegative for `0 ≤ v`. -/
lemma rayleigh_quot_nonneg {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (Ψ : CInfty0Box N L) :
    0 ≤ (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) /
        (√ (∫ x in box N L, ((Ψ : X N → ℝ) x) ^ 2)) ^ 2 := by
  exact div_nonneg (boxEnergy_num_nonneg hL hv Ψ) (sq_nonneg _)

/-! ## There is at least one admissible state -/

/-- For `0 < L` there exists a nonzero smooth function supported in the interior of the box
(a bump state). -/
lemma nonempty_CInfty0Box (N : ℕ) {L : ℝ} (hL : 0 < L) : Nonempty (CInfty0Box N L) := by
  -- centre of the box, coordinate-wise `L / 2`
  let c : X N := fun _ : Fin N => WithLp.toLp 2 (fun _ : Fin 3 => L / 2)
  -- the open coordinate cube strictly inside the box
  let O : Set (X N) := {x | ∀ i : Fin N, ∀ k : Fin 3, (x i) k ∈ Set.Ioo 0 L}
  have hcont (i : Fin N) (k : Fin 3) : Continuous fun x : X N => (x i) k := by fun_prop
  have hOopen : IsOpen O := by
    dsimp [O]
    rw [show {x : X N | ∀ i : Fin N, ∀ k : Fin 3, (x i) k ∈ Set.Ioo 0 L} =
        (⋂ i : Fin N, ⋂ k : Fin 3,
          (fun x : X N => (x i) k) ⁻¹' (Set.Ioo 0 L)) by
          ext x; simp]
    exact isOpen_iInter_of_finite (fun i =>
      isOpen_iInter_of_finite (fun k => IsOpen.preimage (hcont i k) isOpen_Ioo))
  have hcO : c ∈ O := by
    intro i k
    dsimp [c]
    have hpos : 0 < L / 2 := by linarith
    have hlt : L / 2 < L := by linarith
    exact ⟨hpos, hlt⟩
  have hObox : O ⊆ box N L := by
    intro x hx
    rw [mem_box_iff]
    intro i k
    exact Set.Ioo_subset_Icc_self (hx i k)
  have hOint : O ⊆ interior (box N L) := interior_maximal hObox hOopen
  have hO_nhds : O ∈ 𝓝 c := hOopen.mem_nhds hcO
  obtain ⟨f, hts, hcs, hcd, hrange, hfval⟩ :=
    exists_contDiff_tsupport_subset (E := X N) (s := O) (x := c) (n := ⊤) hO_nhds
  refine ⟨⟨f, ?_, ?_, ?_⟩⟩
  · exact hcd.contDiffOn
  · exact hts.trans hOint
  · intro hf0
    have hzero : f c = 0 := congrFun hf0 c
    linarith [hfval]

/-! ## The box energy is non-increasing in the side length -/

set_option linter.style.haveILetI false in
/-- The box energy is non-increasing in the side length: `0 < L1 ≤ L2` implies
`boxEnergy N L2 v ≤ boxEnergy N L1 v`. -/
lemma boxEnergy_antitone {N : ℕ} {L1 L2 : ℝ} (hL1 : 0 < L1) (hLL : L1 ≤ L2)
    {v : ℝ³ → ℝ} (hv : 0 ≤ v) : boxEnergy N L2 v ≤ boxEnergy N L1 v := by
  have hL2 : 0 < L2 := lt_of_lt_of_le hL1 hLL
  let q (L : ℝ) (Φ : CInfty0Box N L) : ℝ :=
    (∫ x in box N L, (Φ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Φ : X N → ℝ) x) /
      (√ (∫ x in box N L, ((Φ : X N → ℝ) x) ^ 2)) ^ 2
  have hbdd : BddBelow (Set.range (q L2)) := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨Φ, rfl⟩
    exact rayleigh_quot_nonneg hL2 hv Φ
  have hmono : ∀ Ψ : CInfty0Box N L1, ∃ Φ : CInfty0Box N L2, q L2 Φ ≤ q L1 Ψ := by
    intro Ψ
    refine ⟨incl hLL Ψ, ?_⟩
    exact le_of_eq (rayleigh_norm_eq_of_le hL1 hLL Ψ)
  have hcineq : (⨅ Φ : CInfty0Box N L2, q L2 Φ) ≤ ⨅ Ψ : CInfty0Box N L1, q L1 Ψ := by
    haveI hne1 : Nonempty (CInfty0Box N L1) := nonempty_CInfty0Box N hL1
    exact le_ciInf fun Ψ => by
      obtain ⟨Φ, hΦ⟩ := hmono Ψ
      exact (ciInf_le hbdd Φ).trans hΦ
  unfold boxEnergy
  simpa [q, pow_two, mul_comm, mul_left_comm, mul_assoc] using hcineq

end BoseGases

end Submission
