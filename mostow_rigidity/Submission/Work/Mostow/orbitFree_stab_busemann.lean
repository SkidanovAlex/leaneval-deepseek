import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.QIDefs

/-! Guidance from the project lead (the requester):

# HL pieces (lead's design) — toward HL: "orbit-free horoball at ζ ⇒ ζ is a cusp" for a lattice with torsion

Plan: HL ⇐ H1 + H2 + H3 + H4a + H4b(open, lead designing).
 H1 orbitFree_stab_busemann: elements of Γ fixing ζ have β := busemann ζ (γ•0) = 0 if the orbit of w₀ avoids a
    horoball at ζ. Proof: cocycle (last clause of HypIsometryProp) with bd γ ζ = ζ gives busemann ζ (γ^k • w₀) =
    busemann ζ w₀ + k·β (induction on k, bd (γ^k) ζ = ζ by POActionProp). If β < 0 take k large ⇒ inside
    horoball ζ s; if β > 0 use γ⁻¹ (β(γ⁻¹) = −β). No discreteness needed.
 H2 stabInfinite_parabolic: Γ discrete, Γ_ζ infinite, β = 0 on Γ_ζ ⇒ Γ_ζ contains a parabolic. Route: (lev, yc)
    coordinates at ζ (QIDefs/levYcFormula/StabHoroForm in the workspace): Γ_ζ acts on the flat ζ^⊥ by y ↦ A y + b.
    Infinite + compact O(n−1) ⇒ infinitely many DISTINCT nontrivial a = g₀⁻¹g with ‖A_a − 1‖ < θ (pigeonhole).
    BT lemma (see NOTES_LEAD_geomFinite_v2.md L5, which works for ANY ζ with β = 0 on Γ_ζ — no parabolic needed):
    only finitely many nontrivial ELLIPTIC elements of Γ_ζ have ‖A − 1‖ < θ₀. So some such a has no fixed point in
    E n; with β(a) = 0 its displacement tends to 0 up the ray to ζ (deepCusp / L1) ⇒ IsParabolic a.
 H3 fordSet_volume_finite: F_ζ := {z | ∀γ, busemann ζ z ≤ busemann ζ (γ•z)}. If Γ_ζ is finite: vol F_ζ ≤ |Γ_ζ|·covol.
    Proof: elements of the finite Γ_ζ have finite order ⇒ β = 0 ⇒ they preserve busemann ζ. For γ ∉ Γ_ζ the tie set
    {z | busemann ζ (γ•z) = busemann ζ z} = {z | busemann (bd γ⁻¹ ζ) z + c = busemann ζ z} is a hyperplane section of
    the hyperboloid (⟨x, θ_η − e^{c}θ_ζ⟩ = 0), volH-null (volH_null_linear). Hence for a.e. z ∈ D (fundamental
    domain, finite volume), #{γ : γ•z ∈ F_ζ} ≤ |Γ_ζ|, and vol F_ζ = ∫_D #{γ : γ z ∈ F_ζ} ≤ |Γ_ζ| vol D.
 H4a fordSet_contains_horoball: orbit of 0 avoids horoball ζ s, and bd γ ζ stays uniformly away from ζ for γ ∉ Γ_ζ
    (1 − ⟪ζ, bd γ ζ⟫ ≥ m > 0) ⇒ F_ζ contains a horoball at ζ. Proof: cocycle with ξ = bd γ⁻¹ ζ:
    busemann ζ (γ•z) = busemann η z + busemann ζ (γ•0), η = bd γ⁻¹ ζ, and busemann ζ (γ•0) ≥ s (orbit-free).
    Minkowski inequality for null θ, θ' and x on the upper sheet: (−⟨x,θ⟩)(−⟨x,θ'⟩) ≥ −⟨θ,θ'⟩/2, i.e.
    busemann ζ z + busemann η z ≥ log((1 − ⟪ζ,η⟫)/2) ≥ log(m/2). So busemann ζ z ≤ (s + log(m/2))/2 ⇒ z ∈ F_ζ
    (for γ ∈ Γ_ζ use H1: β = 0). Take t := (s + log(m/2))/2.
 Consequence: if Γ_ζ is finite and ζ is not an accumulation point of Γ•ζ, H4a gives a horoball in F_ζ, which has
    infinite volH (flat directions unbounded; ∫∫ h^{−n}): contradicts H3. So Γ_ζ infinite ⇒ H2 ⇒ ζ ∈ parFixed.
 H4b (OPEN): Γ_ζ finite AND Γ•ζ accumulates at ζ ⇒ contradiction. Lead is designing it.
-/

namespace Work.Mostow

set_option linter.unusedVariables false

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-- `busemann ξ 0 = 0`. -/
private lemma busemann_self_zero (ξ : E n) : busemann ξ (0 : E n) = 0 := by
  simp [busemann, tpart]

/-- If `g` fixes the boundary point `ξ`, so does every power of `g`. -/
private lemma bd_pow_of_bd_eq (hA : POBasic n) (g : PO n 1) (ξ : E n) (hξ : ξ ∈ Sph n)
    (hg : bd g ξ = ξ) : ∀ k : ℕ, bd (g ^ k) ξ = ξ := by
  intro k
  induction k with
  | zero => rw [pow_zero]; exact hA.bd_one ξ hξ
  | succ k ih =>
      rw [pow_succ, hA.bd_mul (g ^ k) g ξ hξ, hg, ih]

/-- The Busemann cocycle iterated along the powers of an element `g` fixing `ξ`: if `bd g ξ = ξ`,
then `busemann ξ (g^k • u) = busemann ξ u + k * busemann ξ (g • 0)`.  (For a general `g` the
cocycle is twisted by `bd (g^k) ξ`, which is why the fixed-point hypothesis is needed.) -/
private lemma busemann_pow_smul (hA : POBasic n) (hI : HypIsoData n) (g : PO n 1) (ξ : E n)
    (hξ : ξ ∈ Sph n) (hg : bd g ξ = ξ) (u : E n) (k : ℕ) :
    busemann ξ ((g ^ k) • u) = busemann ξ u + (k : ℝ) * busemann ξ (g • (0 : E n)) := by
  induction k generalizing u with
  | zero => rw [pow_zero, hA.one_smul, Nat.cast_zero, zero_mul, add_zero]
  | succ k ih =>
      have hbdk : bd (g ^ k) ξ = ξ := bd_pow_of_bd_eq hA g ξ hξ hg k
      have hc1 := hI.busemann_cocycle (g ^ k) ξ (g • u) hξ
      rw [hbdk] at hc1
      have hc2 := hI.busemann_cocycle g ξ u hξ
      rw [hg] at hc2
      have hc0 := ih (0 : E n)
      rw [busemann_self_zero, zero_add] at hc0
      rw [pow_succ, hA.mul_smul, hc1, hc2, hc0]
      push_cast
      ring

/-- Elements of `Γ` fixing `ζ` and whose orbit of `w₀` avoids the horoball `horoball ζ s` have
`busemann ζ (γ • 0) ≥ 0`.  (This is the Archimedean half of the proof: `β < 0` would drive the
orbit of `w₀` into the horoball.) -/
private lemma busemann_stab_nonneg (hA : POBasic n) (hI : HypIsoData n)
    (Γ : Subgroup (PO n 1)) (w₀ ζ : E n) (hζ : ζ ∈ Sph n) (s : ℝ)
    (hfree : ∀ γ : Γ, (γ : PO n 1) • w₀ ∉ horoball ζ s)
    (γ : Γ) (hγ : bd (γ : PO n 1) ζ = ζ) :
    0 ≤ busemann ζ ((γ : PO n 1) • (0 : E n)) := by
  set β := busemann ζ ((γ : PO n 1) • (0 : E n)) with hβ
  by_contra h
  have hlt : β < 0 := not_le.mp h
  have hge : ∀ k : ℕ, s ≤ busemann ζ w₀ + (k : ℝ) * β := by
    intro k
    have hk := hfree (γ ^ k)
    simp only [horoball, Set.mem_ofPred_eq, not_lt] at hk
    rw [Subgroup.coe_pow] at hk
    have hp := busemann_pow_smul hA hI (γ : PO n 1) ζ hζ hγ w₀ k
    rw [← hβ] at hp
    rwa [hp] at hk
  obtain ⟨k, hk⟩ := exists_nat_gt ((s - busemann ζ w₀) / β)
  have hkb : (k : ℝ) * β < s - busemann ζ w₀ := (div_lt_iff_of_neg hlt).mp hk
  have := hge k
  linarith

theorem orbitFree_stab_busemann (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (w₀ ζ : E n) (hζ : ζ ∈ Sph n) (s : ℝ)
    (hfree : ∀ γ : Γ, (γ : PO n 1) • w₀ ∉ horoball ζ s)
    (γ : Γ) (hγ : bd (γ : PO n 1) ζ = ζ) :
    busemann ζ ((γ : PO n 1) • (0 : E n)) = 0 := by
  have hAb : POBasic n := POBasic.ofProp hA
  have hIb : HypIsoData n := HypIsoData.ofProp hI
  have hnn : 0 ≤ busemann ζ ((γ : PO n 1) • (0 : E n)) :=
    busemann_stab_nonneg hAb hIb Γ w₀ ζ hζ s hfree γ hγ
  -- `γ⁻¹` also fixes `ζ`, because `1 = γ⁻¹ * γ`
  have hinv : bd ((γ : PO n 1)⁻¹) ζ = ζ := by
    have h := hAb.bd_mul ((γ : PO n 1)⁻¹) (γ : PO n 1) ζ hζ
    rw [inv_mul_cancel, hAb.bd_one ζ hζ, hγ] at h
    exact h.symm
  have hnn' : 0 ≤ busemann ζ ((γ : PO n 1)⁻¹ • (0 : E n)) := by
    have h := busemann_stab_nonneg hAb hIb Γ w₀ ζ hζ s hfree (γ⁻¹)
      (by rw [Subgroup.coe_inv]; exact hinv)
    rwa [Subgroup.coe_inv] at h
  -- the cocycle at `u = γ⁻¹ • 0` gives `β + β' = 0`
  have hsum : busemann ζ ((γ : PO n 1) • (0 : E n))
      + busemann ζ ((γ : PO n 1)⁻¹ • (0 : E n)) = 0 := by
    have hc := hIb.busemann_cocycle (γ : PO n 1) ζ ((γ : PO n 1)⁻¹ • (0 : E n)) hζ
    rw [hγ, ← hAb.mul_smul, mul_inv_cancel, hAb.one_smul, busemann_self_zero] at hc
    linarith
  linarith

end Work.Mostow
