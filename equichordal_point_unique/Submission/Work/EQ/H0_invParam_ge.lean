import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.fan_sep

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/EQ/DESIGN.md and DESIGN_CORE.md (orchestrator designs; your lemma is one node). Defs: Submission/Work/EQ/Defs.lean + DefsCore.lean (namespace Work.EQ; do NOT edit). The proved UNIFORMIZATION library is in this workspace (Submission.UnifMain etc.; see DESIGN_CORE 'Library use'). NOTE: importing UnifMain makes `open Topology` resolve to `Work.Topology` — write `open _root_.Topology`.

# H0_invParam_ge: `|ψ₁ψ₂| ≥ ρ` (Rychlik Lemma 17, from Lemma 14) (~1k)

**Route.**
* Separation (Lemma 14). By `fan_estimates`:
  * if `|ψ₁(q)| < δ`, then `q.1 0` is within `1/4` (semi-projective) of an axis point in `-1/2+2ℤ`;
  * if `|ψ₂(q)| < δ`, then `q.1 0` is within `1/4` of an axis point in `1/2+2ℤ` (mirror).
  Both cannot hold, since the distance is 1.
* Given `|ψ₁ψ₂| < ρ := δ² λ`, apply `hShift` `j` times (it changes `ψ₁` by `λ^j` and `ψ₂` by
  `λ^{-j}`). This brings both below `δ` in modulus, a contradiction.
* Rychlik's choice is `ρ = δ²(λ₁/λ₂)`, with `λ₂ = 1/λ`.

## Implementation notes (this file)

The proof is self-contained apart from one input: the uniform fan separation estimate
`Work.EQ.fan_sep` (Rychlik Theorem 7(1) + Lemma 14), which is the hypothesis `hfan` of
`H0_invParam_ge_of_fan`; the target `H0_invParam_ge` is derived from it at the end.

Structural ingredients proved here from the definitions:
* `H0_invParam_ge_exists_invBranch`: a *regular pair* determines its branch: from
  `EqRelC a P Q` and `(Q.1 + a/2)^2 + Q.2^2 ≠ 0` one gets `P = invBranch a s Q` for one of the
  two signs (pure algebra with the bilinear square norm).
* `H0_invParam_ge_eqRelC_mirror`, `H0_invParam_ge_regPair_mirror`: the bisector reflection
  `eqMirror` conjugates the relation to its inverse: it maps `RegPair a P Q` to
  `RegPair a (eqMirror Q) (eqMirror P)`.
* `shiftZ` (`ψ₁ ↦ λ^j ψ₁`, `ψ₂ ↦ ψ₂/λ^j`, index shift by `j ∈ ℤ`) maps chains to chains and `H0`
  to `H0` (the local continuous family is re-parametrised).
* `mirrorChain`: the bisector-reflected chain, with the two linearising parameters exchanged.
  It produces the *unstable* fan, hence the coset `1/2 + 2ℤ`.
* `chain_eq_fan`: the `0`-th point of a chain *is* a fan value, `p.1 0 = fan a h ε p.2.1`, read
  off from the forward tail `p.1 n = germC (λ^n ψ₁)` by induction.
-/

namespace Work.EQ

open Filter _root_.Topology
open Complex

noncomputable section

/-! ## Elementary facts about `λ = eqLam a` -/

private theorem eqLam_pos_of {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < eqLam a := by
  rw [eqLam]; exact div_pos (by linarith) (by linarith)

private theorem eqLam_lt_one_of {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]; linarith

private theorem eqLam_ne_zero_of {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a ≠ 0 :=
  ne_of_gt (eqLam_pos_of ha0 ha1)

private theorem eqLamC_ne_zero_of {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ((eqLam a : ℝ) : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_zero, ne_eq, Complex.ofReal_inj]
  exact eqLam_ne_zero_of ha0 ha1

private theorem norm_lamC_zpow {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℤ) :
    ‖((eqLam a : ℝ) : ℂ) ^ j‖ = eqLam a ^ j := by
  have h : (0 : ℝ) < eqLam a := eqLam_pos_of ha0 ha1
  rw [norm_zpow]
  simp [abs_of_pos h]

/-! ## Identities in `ℤ`-powers of `λ` -/

private theorem zpow_sub_mul {c : ℂ} (hc : c ≠ 0) (n j : ℤ) (z : ℂ) :
    c ^ n * (z / c ^ j) = c ^ (n - j) * z := by
  rw [div_eq_mul_inv, ← zpow_neg]
  conv_rhs => rw [show n - j = n + -j by ring, zpow_add₀ hc]
  ring

private theorem zpow_add_mul {c : ℂ} (hc : c ≠ 0) (n j : ℤ) (z : ℂ) :
    c ^ (n + j) * z = c ^ n * (c ^ j * z) := by
  rw [zpow_add₀ hc]; ring

/-! ## The algebra of the equichordal relation -/

/-- **A regular pair determines the backward branch.** If `(P,Q)` satisfies the polynomial
equichordal relation and `Q` is off the isotropic lines through `O₁ = (-a/2,0)`, i.e.
`(Q.1 + a/2)^2 + Q.2^2 ≠ 0`, then `P` is one of the two backward local branches of `Q`. -/
theorem H0_invParam_ge_exists_invBranch {a : ℝ} {P Q : ℂ × ℂ} (h : EqRelC a P Q)
    (hb : (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2 ≠ 0) :
    P = invBranch a true Q ∨ P = invBranch a false Q := by
  have hs : (Q.1 + P.1) ^ 2 + (Q.2 + P.2) ^ 2 = 1 := h.1
  have h2 : (Q.1 + P.1) * P.2 = (Q.2 + P.2) * (P.1 - ((a / 2 : ℝ) : ℂ)) := h.2
  have hcross : (Q.1 + P.1) * Q.2 = (Q.2 + P.2) * (Q.1 + ((a / 2 : ℝ) : ℂ)) := by
    linear_combination (norm := ring_nf) -h2
  set A : ℂ := Q.1 + P.1 with hA
  set B : ℂ := Q.2 + P.2 with hB
  set v1 : ℂ := Q.1 + ((a / 2 : ℝ) : ℂ) with hv1
  set v2 : ℂ := Q.2 with hv2
  have hA' : A = Q.1 + P.1 := hA
  have hB' : B = Q.2 + P.2 := hB
  have hcross' : A * v2 = B * v1 := by rw [hA', hB', hv1, hv2]; exact hcross
  have hs' : A ^ 2 + B ^ 2 = 1 := by rw [hA', hB']; exact hs
  have hv : v1 ^ 2 + v2 ^ 2 ≠ 0 := hb
  have hdep : ∃ t : ℂ, A = t * v1 ∧ B = t * v2 := by
    rcases eq_or_ne v1 0 with hv10 | hv10
    · have hv2ne : v2 ≠ 0 := by
        intro h0; exact hv (by rw [hv10, h0]; ring)
      refine ⟨B / v2, ?_, ?_⟩
      · rw [hv10, mul_zero]
        have hzero : A * v2 = 0 := by rw [hcross', hv10, mul_zero]
        exact (mul_eq_zero.mp hzero).resolve_right hv2ne
      · exact (div_mul_cancel₀ B hv2ne).symm
    · refine ⟨A / v1, ?_, ?_⟩
      · exact (div_mul_cancel₀ A hv10).symm
      · rw [div_mul_eq_mul_div]
        exact (eq_div_iff hv10).mpr hcross'.symm
  obtain ⟨t, htA, htB⟩ := hdep
  have htsq : t ^ 2 * (v1 ^ 2 + v2 ^ 2) = 1 := by
    have hh : A ^ 2 + B ^ 2 = t ^ 2 * (v1 ^ 2 + v2 ^ 2) := by rw [htA, htB]; ring
    rw [← hh]; exact hs'
  set R : ℂ := (v1 ^ 2 + v2 ^ 2) ^ (1 / 2 : ℂ) with hR
  have hR2 : R ^ 2 = v1 ^ 2 + v2 ^ 2 := by
    rw [hR, show (1 / 2 : ℂ) = ((2 : ℂ))⁻¹ by norm_num]
    exact Complex.cpow_nat_inv_pow (v1 ^ 2 + v2 ^ 2) (n := 2) (by norm_num)
  have hRne : R ≠ 0 := by
    intro h0
    rw [h0] at hR2
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hR2
    exact hv hR2.symm
  have htr : (t * R) ^ 2 = 1 := by rw [mul_pow, hR2]; exact htsq
  have hP1 : P.1 = A - Q.1 := by rw [hA']; ring
  have hP2 : P.2 = B - Q.2 := by rw [hB']; ring
  have hvc : ((a / 2 : ℝ) : ℂ) = v1 - Q.1 := by rw [hv1]; ring
  have hRdef : R = ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ^ (1 / 2 : ℂ) := by
    rw [hR, hv1, hv2]
  rcases sq_eq_one_iff.mp htr with h1 | h1
  · left
    have ht : t = 1 / R := by rw [eq_div_iff hRne]; exact h1
    have e1 : P.1 = -Q.1 + 1 * (Q.1 + ((a / 2 : ℝ) : ℂ)) / R := by
      rw [show P.1 = t * v1 - Q.1 by rw [hP1, htA]]
      rw [ht, hvc]; ring
    have e2 : P.2 = -Q.2 + 1 * Q.2 / R := by
      rw [show P.2 = t * v2 - Q.2 by rw [hP2, htB, hv2]]
      rw [ht]; ring
    refine Prod.ext ?_ ?_
    · rw [e1]; simp only [invBranch, hRdef]; norm_num
    · rw [e2]; simp only [invBranch, hRdef]; norm_num
  · right
    have ht : t = (-1) / R := by rw [eq_div_iff hRne]; exact h1
    have e1 : P.1 = -Q.1 + (-1) * (Q.1 + ((a / 2 : ℝ) : ℂ)) / R := by
      rw [show P.1 = t * v1 - Q.1 by rw [hP1, htA]]
      rw [ht, hvc]; ring
    have e2 : P.2 = -Q.2 + (-1) * Q.2 / R := by
      rw [show P.2 = t * v2 - Q.2 by rw [hP2, htB, hv2]]
      rw [ht]; ring
    refine Prod.ext ?_ ?_
    · rw [e1]; simp only [invBranch, hRdef]; norm_num
    · rw [e2]; simp only [invBranch, hRdef]; norm_num

/-- The bisector reflection conjugates the equichordal relation to its inverse. -/
theorem H0_invParam_ge_eqRelC_mirror {a : ℝ} {P Q : ℂ × ℂ} :
    EqRelC a (eqMirror Q) (eqMirror P) ↔ EqRelC a P Q := by
  simp only [eqMirror, EqRelC]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have : (-P.1 + -Q.1) ^ 2 + (P.2 + Q.2) ^ 2
          = (Q.1 + P.1) ^ 2 + (Q.2 + P.2) ^ 2 := by ring
      rw [this] at h1; exact h1
    · linear_combination (norm := ring_nf) h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have : (-P.1 + -Q.1) ^ 2 + (P.2 + Q.2) ^ 2
          = (Q.1 + P.1) ^ 2 + (Q.2 + P.2) ^ 2 := by ring
      rw [this]; exact h1
    · linear_combination (norm := ring_nf) h2

private theorem eqMirror_den1 (a : ℝ) (Q : ℂ × ℂ) :
    ((eqMirror Q).1 - ((a / 2 : ℝ) : ℂ)) ^ 2 + (eqMirror Q).2 ^ 2
      = (Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2 := by
  simp only [eqMirror]; ring

private theorem eqMirror_den2 (a : ℝ) (P : ℂ × ℂ) :
    ((eqMirror P).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (eqMirror P).2 ^ 2
      = (P.1 - ((a / 2 : ℝ) : ℂ)) ^ 2 + P.2 ^ 2 := by
  simp only [eqMirror]; ring

/-- `RegPair` is invariant under the bisector reflection, with the two arguments swapped. -/
theorem H0_invParam_ge_regPair_mirror {a : ℝ} {P Q : ℂ × ℂ} :
    RegPair a (eqMirror Q) (eqMirror P) ↔ RegPair a P Q := by
  unfold RegPair
  rw [H0_invParam_ge_eqRelC_mirror, eqMirror_den1 a Q, eqMirror_den2 a P]
  tauto

/-! ## The integer shift of chain data -/

/-- The shift `σ^j` of chain data for `j : ℤ`: `Pₙ ↦ P_{n+j}`, `ψ₁ ↦ λ^j ψ₁`,
`ψ₂ ↦ ψ₂/λ^j`. For `j = 1` this is `hShift`. -/
noncomputable def shiftZ (a : ℝ) (j : ℤ) (p : ChainData) : ChainData :=
  (fun n => p.1 (n + j), ((eqLam a : ℝ) : ℂ) ^ j * p.2.1, p.2.2 / ((eqLam a : ℝ) : ℂ) ^ j)

@[simp] theorem shiftZ_fst (a : ℝ) (j : ℤ) (p : ChainData) (n : ℤ) :
    (shiftZ a j p).1 n = p.1 (n + j) := rfl

@[simp] theorem shiftZ_psi1 (a : ℝ) (j : ℤ) (p : ChainData) :
    (shiftZ a j p).2.1 = ((eqLam a : ℝ) : ℂ) ^ j * p.2.1 := rfl

@[simp] theorem shiftZ_psi2 (a : ℝ) (j : ℤ) (p : ChainData) :
    (shiftZ a j p).2.2 = p.2.2 / ((eqLam a : ℝ) : ℂ) ^ j := rfl

theorem continuous_shiftZ (a : ℝ) (j : ℤ) : Continuous (shiftZ a j) := by
  unfold shiftZ
  fun_prop

/-- The forward tail, in `ℤ`-indexed form. -/
private theorem tail_fwd {a : ℝ} {h : ℂ → ℂ} {p : ChainData}
    (hfwd : ∀ᶠ n : ℕ in atTop,
      p.1 n = germC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.1)) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ m →
      p.1 m = germC a h (((eqLam a : ℝ) : ℂ) ^ m * p.2.1) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hfwd
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k :=
    ⟨m.toNat, (Int.toNat_of_nonneg (le_trans (by positivity) hm)).symm⟩
  simpa using hN k (by exact_mod_cast hm)

/-- The backward tail, in `ℤ`-indexed form. -/
private theorem tail_bwd {a : ℝ} {h : ℂ → ℂ} {p : ChainData}
    (hbwd : ∀ᶠ n : ℕ in atTop,
      p.1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.2)) :
    ∃ N : ℕ, ∀ m : ℤ, (N : ℤ) ≤ m →
      p.1 (-m) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * p.2.2) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbwd
  refine ⟨N, fun m hm => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = k :=
    ⟨m.toNat, (Int.toNat_of_nonneg (le_trans (by positivity) hm)).symm⟩
  simpa using hN k (by exact_mod_cast hm)

/-- The shift `σ^j` maps chains to chains. -/
theorem isChain_shiftZ {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {p : ChainData}
    (hp : IsChain a h p) (j : ℤ) : IsChain a h (shiftZ a j p) := by
  obtain ⟨hreg, h1, h2, hfwd, hbwd⟩ := hp
  have hlamC : ((eqLam a : ℝ) : ℂ) ≠ 0 := eqLamC_ne_zero_of ha0 ha1
  obtain ⟨N₁, hN₁⟩ := tail_fwd hfwd
  obtain ⟨N₂, hN₂⟩ := tail_bwd hbwd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [shiftZ_fst, shiftZ_fst, show n + 1 + j = (n + j) + 1 by ring]
    exact hreg (n + j)
  · rw [shiftZ_psi1]
    exact mul_ne_zero (zpow_ne_zero j hlamC) h1
  · rw [shiftZ_psi2]
    exact div_ne_zero h2 (zpow_ne_zero j hlamC)
  · filter_upwards [eventually_ge_atTop (((N₁ : ℤ) - j).toNat)] with n hn
    rw [shiftZ_fst, shiftZ_psi1]
    have h1' : (N₁ : ℤ) ≤ (n : ℤ) + j := by omega
    rw [hN₁ _ h1']
    exact congrArg (germC a h) (zpow_add_mul hlamC (n : ℤ) j p.2.1)
  · filter_upwards [eventually_ge_atTop (((N₂ : ℤ) + j).toNat)] with n hn
    rw [shiftZ_fst, shiftZ_psi2]
    have h1' : (N₂ : ℤ) ≤ (n : ℤ) - j := by omega
    rw [show -(n : ℤ) + j = -((n : ℤ) - j) by ring, hN₂ _ h1']
    exact congrArg (ugermC a h) (zpow_sub_mul hlamC (n : ℤ) j p.2.2).symm

/-- The shift `σ^j` maps `H0` to itself. -/
theorem mem_H0_shiftZ {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {p : ChainData}
    (hp : p ∈ H0 a h) (j : ℤ) : shiftZ a j p ∈ H0 a h := by
  obtain ⟨ε, hε, f, hcont, hf0, hf⟩ := hp
  have hlamC : ((eqLam a : ℝ) : ℂ) ≠ 0 := eqLamC_ne_zero_of ha0 ha1
  have hlam0 : (0 : ℝ) < eqLam a := eqLam_pos_of ha0 ha1
  have hpowpos : (0 : ℝ) < eqLam a ^ j := zpow_pos hlam0 j
  have hmap : ∀ u ∈ Metric.ball (shiftZ a j p).2.1 (eqLam a ^ j * ε),
      u / ((eqLam a : ℝ) : ℂ) ^ j ∈ Metric.ball p.2.1 ε := by
    intro u hu
    rw [Metric.mem_ball] at hu
    rw [dist_eq_norm] at hu
    rw [show (shiftZ a j p).2.1 = ((eqLam a : ℝ) : ℂ) ^ j * p.2.1 from shiftZ_psi1 a j p] at hu
    rw [Metric.mem_ball, dist_eq_norm,
      show u / ((eqLam a : ℝ) : ℂ) ^ j - p.2.1
        = (u - ((eqLam a : ℝ) : ℂ) ^ j * p.2.1) / ((eqLam a : ℝ) : ℂ) ^ j from div_sub' (zpow_ne_zero j hlamC)]
    rw [norm_div, norm_lamC_zpow ha0 ha1 j, div_lt_iff₀ (zpow_pos hlam0 j)]
    calc ‖u - ((eqLam a : ℝ) : ℂ) ^ j * p.2.1‖ < eqLam a ^ j * ε := hu
      _ = ε * eqLam a ^ j := by ring
  refine ⟨eqLam a ^ j * ε, by positivity,
    fun u => shiftZ a j (f (u / ((eqLam a : ℝ) : ℂ) ^ j)), ?_, ?_, ?_⟩
  · exact (continuous_shiftZ a j).comp_continuousOn
      (hcont.comp (continuous_id.div_const _).continuousOn hmap)
  · show shiftZ a j (f ((((eqLam a : ℝ) : ℂ) ^ j * p.2.1) / ((eqLam a : ℝ) : ℂ) ^ j))
        = shiftZ a j p
    rw [mul_div_cancel_left₀ p.2.1 (zpow_ne_zero j hlamC), hf0]
  · intro u hu
    have hmem := hmap u hu
    refine ⟨isChain_shiftZ ha0 ha1 (hf _ hmem).1 j, ?_⟩
    rw [shiftZ_psi1, (hf _ hmem).2, mul_comm,
      div_mul_cancel₀ _ (zpow_ne_zero j hlamC)]

/-! ## The mirrored chain -/

/-- The bisector-reflected chain: the two linearising parameters are exchanged. -/
noncomputable def mirrorChain (p : ChainData) : ChainData :=
  (fun n => eqMirror (p.1 (-n)), p.2.2, p.2.1)

@[simp] theorem mirrorChain_fst (p : ChainData) (n : ℤ) :
    (mirrorChain p).1 n = eqMirror (p.1 (-n)) := rfl

@[simp] theorem mirrorChain_psi1 (p : ChainData) : (mirrorChain p).2.1 = p.2.2 := rfl

@[simp] theorem mirrorChain_psi2 (p : ChainData) : (mirrorChain p).2.2 = p.2.1 := rfl

theorem mirrorChain_fst_zero (p : ChainData) : (mirrorChain p).1 0 = eqMirror (p.1 0) := by
  simp

/-- The mirror of a chain is a chain (with the two tails exchanged). -/
theorem isChain_mirrorChain {a : ℝ} {h : ℂ → ℂ} {p : ChainData} (hp : IsChain a h p) :
    IsChain a h (mirrorChain p) := by
  obtain ⟨hreg, h1, h2, hfwd, hbwd⟩ := hp
  obtain ⟨N₁, hN₁⟩ := tail_fwd hfwd
  obtain ⟨N₂, hN₂⟩ := tail_bwd hbwd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [mirrorChain_fst, mirrorChain_fst]
    refine (H0_invParam_ge_regPair_mirror).mpr ?_
    rw [show -n = (-(n + 1)) + 1 by ring]
    exact hreg (-(n + 1))
  · rw [mirrorChain_psi1]; exact h2
  · rw [mirrorChain_psi2]; exact h1
  · filter_upwards [eventually_ge_atTop N₂] with n hn
    rw [mirrorChain_fst, mirrorChain_psi1]
    rw [show -(↑n : ℤ) = -(↑n) by ring, hN₂ _ (by exact_mod_cast hn)]
    simp [ugermC, eqMirror]
  · filter_upwards [eventually_ge_atTop N₁] with n hn
    rw [mirrorChain_fst, mirrorChain_psi2]
    rw [show -(-(↑n : ℤ)) = (↑n : ℤ) by ring, hN₁ _ (by exact_mod_cast hn)]
    rfl

/-! ## Reading a chain as a fan value -/

/-- The `0`-th point of a chain is a fan value with the chain's own linearising parameter
`s = ψ₁`. -/
theorem chain_eq_fan {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} :
    ∀ (N : ℕ) (p : ChainData), IsChain a h p →
      (∀ n : ℕ, N ≤ n → p.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * p.2.1)) →
      ∃ ε : List Bool, p.1 0 = fan a h ε p.2.1 := by
  intro N
  induction N with
  | zero =>
    intro p hp htail
    refine ⟨[], ?_⟩
    rw [show p.1 (0 : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ (0 : ℕ) * p.2.1) from htail 0 le_rfl]
    simp [fan]
  | succ N ih =>
    intro p hp htail
    have hp' : IsChain a h (shiftZ a 1 p) := isChain_shiftZ ha0 ha1 hp 1
    have htail' : ∀ n : ℕ, N ≤ n →
        (shiftZ a 1 p).1 (n : ℤ) =
          germC a h (((eqLam a : ℝ) : ℂ) ^ n * (shiftZ a 1 p).2.1) := by
      intro n hn
      rw [shiftZ_fst, shiftZ_psi1, zpow_one]
      have hcast : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hcast, htail (n + 1) (by omega)]
      congr 1
      rw [pow_succ]; ring
    obtain ⟨ε, hε⟩ := ih (shiftZ a 1 p) hp' htail'
    have hfst : p.1 1 = fan a h ε (((eqLam a : ℝ) : ℂ) * p.2.1) := by
      have h0 : (shiftZ a 1 p).1 0 = p.1 1 := by rw [shiftZ_fst]; norm_num
      rw [← h0, hε, shiftZ_psi1, zpow_one]
    have hreg0 : RegPair a (p.1 0) (p.1 1) := by
      simpa using hp.1 0
    rcases H0_invParam_ge_exists_invBranch hreg0.1 hreg0.2.2 with h | h
    · refine ⟨true :: ε, ?_⟩
      rw [show p.1 0 = invBranch a true (p.1 1) from h, hfst]
      rfl
    · refine ⟨false :: ε, ?_⟩
      rw [show p.1 0 = invBranch a false (p.1 1) from h, hfst]
      rfl

/-- **The `0`-th point of a chain is a fan value.** -/
theorem chain_eq_fan' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {p : ChainData}
    (hp : IsChain a h p) : ∃ ε : List Bool, p.1 0 = fan a h ε p.2.1 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hp.2.2.2.1
  exact chain_eq_fan ha0 ha1 N p hp fun n hn => hN n hn

/-! ## The arithmetic of the shift: balancing the two linearising parameters -/

/-- For `0 < c < 1`, `x > 0`, `δ > 0` there is an integer `j` with `c^j x ∈ [cδ, δ)`. -/
private theorem exists_zpow_mem_Ico {c x δ : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hx : 0 < x)
    (hδ : 0 < δ) : ∃ j : ℤ, c * δ ≤ c ^ j * x ∧ c ^ j * x < δ := by
  have hcδ : (0 : ℝ) < c * δ := by positivity
  by_cases hxd : x < δ
  · by_cases h1 : c * δ ≤ x
    · exact ⟨0, by rw [zpow_zero, one_mul]; exact ⟨h1, hxd⟩⟩
    · have hr : 0 < x / (c * δ) := div_pos hx hcδ
      have hex : ∃ k : ℕ, c ^ k ≤ x / (c * δ) := by
        have hlim : Tendsto (fun k : ℕ => c ^ k) atTop (𝓝 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one hc0.le hc1
        exact (hlim.eventually (eventually_le_nhds hr)).exists
      set K := Nat.find hex with hKdef
      have hKle : c ^ K ≤ x / (c * δ) := Nat.find_spec hex
      have hKmin : ∀ k < K, ¬ (c ^ k ≤ x / (c * δ)) := fun k hk => Nat.find_min hex hk
      have hKpos : 0 < K := by
        rcases Nat.eq_zero_or_pos K with h | h
        · exfalso
          rw [h, pow_zero] at hKle
          have hcl : c * δ ≤ x := by
            have h' := (le_div_iff₀ hcδ).mp hKle
            simpa using h'
          linarith
        · exact h
      refine ⟨-(K : ℤ), ?_, ?_⟩
      · rw [zpow_neg, zpow_natCast, inv_mul_eq_div, le_div_iff₀ (pow_pos hc0 K)]
        calc c * δ * c ^ K = c ^ K * (c * δ) := by ring
          _ ≤ (x / (c * δ)) * (c * δ) := mul_le_mul_of_nonneg_right hKle hcδ.le
          _ = x := by field_simp
      · obtain ⟨K', hK'⟩ : ∃ K' : ℕ, K = K' + 1 := ⟨K - 1, by omega⟩
        have hmin' : x / (c * δ) < c ^ K' := not_le.mp (hKmin K' (by omega))
        rw [zpow_neg, zpow_natCast, inv_mul_eq_div, div_lt_iff₀ (pow_pos hc0 K)]
        rw [hK', pow_succ]
        have hstep : x / c ^ K' < c * δ := by
          rw [div_lt_iff₀ (pow_pos hc0 K')]
          calc x = (x / (c * δ)) * (c * δ) := by field_simp
            _ < c ^ K' * (c * δ) := mul_lt_mul_of_pos_right hmin' hcδ
            _ = (c * δ) * c ^ K' := by ring
        calc x = c ^ K' * (x / c ^ K') := by field_simp
          _ < c ^ K' * (c * δ) := mul_lt_mul_of_pos_left hstep (pow_pos hc0 K')
          _ = δ * (c ^ K' * c) := by ring
  · have hex : ∃ k : ℕ, c ^ k * x < δ := by
      have hlim : Tendsto (fun k : ℕ => c ^ k * x) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0.le hc1).mul_const x
      exact (hlim.eventually (Iio_mem_nhds hδ)).exists
    set m := Nat.find hex with hmdef
    have hm : c ^ m * x < δ := Nat.find_spec hex
    have hmmin : ∀ k < m, ¬ (c ^ k * x < δ) := fun k hk => Nat.find_min hex hk
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exfalso; rw [h, pow_zero, one_mul] at hm; linarith
      · exact h
    refine ⟨(m : ℤ), ?_, ?_⟩
    · rw [zpow_natCast]
      obtain ⟨m', hm'⟩ : ∃ m' : ℕ, m = m' + 1 := ⟨m - 1, by omega⟩
      have hmin' : δ ≤ c ^ m' * x := not_lt.mp (hmmin m' (by omega))
      rw [hm', pow_succ]
      calc c * δ ≤ c * (c ^ m' * x) := mul_le_mul_of_nonneg_left hmin' hc0.le
        _ = c ^ m' * c * x := by ring
    · rw [zpow_natCast]; exact hm

/-! ## The main estimate: `|ψ₁ψ₂| ≥ ρ` on `H0` -/

/-- **The invariant parameter is bounded below**, in the form that only needs the uniform fan
separation estimate (Rychlik's Lemma 14 separation input). -/
theorem H0_invParam_ge_of_fan {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (_hh : IsStableGerm a h r)
    (hfan : ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : List Bool) (u : ℂ), u ∈ Metric.ball (0 : ℂ) δ →
      (fan a h ε 0).2 = 0 ∧ (∃ k : ℤ, (fan a h ε 0).1 = -1 / 2 + 2 * k) ∧
      ‖(fan a h ε u).1 - (fan a h ε 0).1‖ ≤ 1 / 4) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ H0 a h, ρ ≤ ‖q.2.1 * q.2.2‖ := by
  obtain ⟨δ, hδ, hfan⟩ := hfan
  have hlam0 : (0 : ℝ) < eqLam a := eqLam_pos_of ha0 ha1
  have hlam1 : eqLam a < 1 := eqLam_lt_one_of ha0 ha1
  have hlamC : ((eqLam a : ℝ) : ℂ) ≠ 0 := eqLamC_ne_zero_of ha0 ha1
  refine ⟨δ ^ 2 * eqLam a, by positivity, fun q hq => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  -- `q` is a chain
  obtain ⟨ε₀, hε₀, f, hcont, hf0, hfam⟩ := hq
  have hchain : IsChain a h q := by
    have hmem : q.2.1 ∈ Metric.ball q.2.1 ε₀ := by
      rw [Metric.mem_ball, dist_self]; exact hε₀
    rw [← hf0]; exact (hfam q.2.1 hmem).1
  have hq1 : q.2.1 ≠ 0 := hchain.2.1
  have hn1 : (0 : ℝ) < ‖q.2.1‖ := norm_pos_iff.mpr hq1
  -- choose the shift balancing `ψ₁` and `ψ₂`
  obtain ⟨j, hj1, hj2⟩ := exists_zpow_mem_Ico hlam0 hlam1 hn1 hδ
  set q' : ChainData := shiftZ a j q with hq'def
  have hchain' : IsChain a h q' := isChain_shiftZ ha0 ha1 hchain j
  have hpsi1 : q'.2.1 = ((eqLam a : ℝ) : ℂ) ^ j * q.2.1 := shiftZ_psi1 a j q
  have hpsi2 : q'.2.2 = q.2.2 / ((eqLam a : ℝ) : ℂ) ^ j := shiftZ_psi2 a j q
  have hlt1 : ‖q'.2.1‖ < δ := by
    rw [hpsi1, norm_mul, norm_lamC_zpow ha0 ha1 j]; exact hj2
  have hj1' : eqLam a * δ ≤ ‖q'.2.1‖ := by rw [hpsi1, norm_mul, norm_lamC_zpow ha0 ha1 j]; exact hj1
  have hlt2 : ‖q'.2.2‖ < δ := by
    have h1 : ‖q'.2.2‖ = ‖q.2.1 * q.2.2‖ / ‖q'.2.1‖ := by
      rw [hpsi2, norm_div, norm_lamC_zpow ha0 ha1 j, norm_mul, hpsi1,
        norm_mul, norm_lamC_zpow ha0 ha1 j]
      field_simp
    rw [h1]
    have hpos : (0 : ℝ) < eqLam a * δ := by positivity
    calc ‖q.2.1 * q.2.2‖ / ‖q'.2.1‖ ≤ ‖q.2.1 * q.2.2‖ / (eqLam a * δ) :=
          div_le_div_of_nonneg_left (norm_nonneg _) hpos hj1'
      _ < δ ^ 2 * eqLam a / (eqLam a * δ) := div_lt_div_of_pos_right hcon hpos
      _ = δ := by field_simp
  -- the fan value of `q'.1 0` and the axis point of the coset `-1/2 + 2ℤ`
  obtain ⟨ε₁, hε₁⟩ := chain_eq_fan' ha0 ha1 hchain'
  have hmem1 : q'.2.1 ∈ Metric.ball (0 : ℂ) δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hlt1
  have hk₁ : ∃ k : ℤ, (fan a h ε₁ 0).1 = -1 / 2 + 2 * k := (hfan ε₁ q'.2.1 hmem1).2.1
  have hb₁ : ‖(fan a h ε₁ q'.2.1).1 - (fan a h ε₁ 0).1‖ ≤ 1 / 4 :=
    (hfan ε₁ q'.2.1 hmem1).2.2
  -- the same for the mirror chain, which gives the coset `1/2 + 2ℤ`
  set q'' : ChainData := mirrorChain q' with hq''def
  have hchain'' : IsChain a h q'' := isChain_mirrorChain hchain'
  have hlt2' : ‖q''.2.1‖ < δ := by rw [mirrorChain_psi1]; exact hlt2
  obtain ⟨ε₂, hε₂⟩ := chain_eq_fan' ha0 ha1 hchain''
  have hmem2 : q''.2.1 ∈ Metric.ball (0 : ℂ) δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hlt2'
  have hk₂ : ∃ k : ℤ, (fan a h ε₂ 0).1 = -1 / 2 + 2 * k := (hfan ε₂ q''.2.1 hmem2).2.1
  have hb₂ : ‖(fan a h ε₂ q''.2.1).1 - (fan a h ε₂ 0).1‖ ≤ 1 / 4 :=
    (hfan ε₂ q''.2.1 hmem2).2.2
  -- the two estimates are about the same real point, up to sign
  have hx₁ : (fan a h ε₁ q'.2.1).1 = (q'.1 0).1 := by rw [hε₁]
  have hx₂ : (fan a h ε₂ q''.2.1).1 = -(q'.1 0).1 := by
    rw [← hε₂, mirrorChain_fst_zero]
    rfl
  -- the axis points differ by an odd integer
  obtain ⟨k₁, hk₁'⟩ := hk₁
  obtain ⟨k₂, hk₂'⟩ := hk₂
  have hsum : (fan a h ε₁ 0).1 + (fan a h ε₂ 0).1 = (((-1 + 2 * (k₁ + k₂) : ℤ)) : ℂ) := by
    rw [hk₁', hk₂']; push_cast; ring
  have hsmall : ‖(fan a h ε₁ 0).1 + (fan a h ε₂ 0).1‖ ≤ 1 / 2 := by
    have e1 : ‖(fan a h ε₁ 0).1 - (q'.1 0).1‖ ≤ 1 / 4 := by
      rw [← hx₁]; simpa [norm_sub_rev] using hb₁
    have e2 : ‖(q'.1 0).1 + (fan a h ε₂ 0).1‖ ≤ 1 / 4 := by
      have h3 : ‖(-(q'.1 0).1) - (fan a h ε₂ 0).1‖ ≤ 1 / 4 := by rw [← hx₂]; exact hb₂
      rw [show -(q'.1 0).1 - (fan a h ε₂ 0).1 = -((q'.1 0).1 + (fan a h ε₂ 0).1) by ring,
        norm_neg] at h3
      exact h3
    calc ‖(fan a h ε₁ 0).1 + (fan a h ε₂ 0).1‖
        = ‖(fan a h ε₁ 0).1 - (q'.1 0).1 + ((q'.1 0).1 + (fan a h ε₂ 0).1)‖ := by ring_nf
      _ ≤ ‖(fan a h ε₁ 0).1 - (q'.1 0).1‖ + ‖(q'.1 0).1 + (fan a h ε₂ 0).1‖ :=
          norm_add_le _ _
      _ ≤ 1 / 2 := by linarith
  have hbig : (1 : ℝ) ≤ ‖(fan a h ε₁ 0).1 + (fan a h ε₂ 0).1‖ := by
    rw [hsum, Complex.norm_intCast]
    have hm : (-1 + 2 * (k₁ + k₂) : ℤ) ≠ 0 := by omega
    have h1 := Int.one_le_abs hm
    exact_mod_cast h1
  linarith

/-- **The invariant parameter is bounded below (Rychlik Lemma 17, from Lemma 14).** -/
theorem H0_invParam_ge {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ H0 a h, ρ ≤ ‖q.2.1 * q.2.2‖ := by
  obtain ⟨δ, hδ, h⟩ := fan_sep ha0 ha1 hh
  exact H0_invParam_ge_of_fan ha0 ha1 hh
    ⟨δ, hδ, fun ε u hu => ⟨(h ε u hu).1, (h ε u hu).2.1, (h ε u hu).2.2.1⟩⟩

end

end Work.EQ
