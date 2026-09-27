import Mathlib
import Submission.Mostow.GeodDefs

/-! Guidance from the project lead (the requester):

# Geodesic strata (k = 1 case of GAP-A, odd n ≥ 5) — lead's design (reviewed). Vocabulary Submission/Mostow/GeodDefs.lean
# (fermiW, rotN) on top of SubHypDefs/HLDefs. Your request carries an exact statement; the design text below gives the
# route for the whole k = 1 chain (L1–L12). fermiW v W = (√(1+‖W‖²)·v, W) is the same point as fermi v w with
# W = sinhc‖w‖·w, so blk acts by (v,W) ↦ (h v, R W) (use blk_smul_fermi, being proved as Work.Mostow.blk_smul_fermi).
# For k = 1 the hyperbolic volume in (v,W) coordinates is EXACTLY volH 1 ⊗ Lebesgue (Jacobian √(1+‖W‖²) cancels tpart).
# λ is a reserved token — never use it as a variable name.
=================================================================================================================
**The k = 1 case of GAP-A closes for odd n = 1+m ≥ 5.** For every η ≤ η₀(n,V) there is an infinite-order γ with d(z,γz) ≤ C_n·η, which is stronger than the requested C(1+V)η. The degenerate case, non-centralising g₀ and equal-angle blocks are all covered. Kazhdan–Margulis is used exactly once, in the gap lemma L3 below, which is certain given the chapter's existing inputs. The stable window (1), the thickened torus-orbit tube (2) and KM on 2-planes (3) are not needed. Three new ideas replace them: exact Euclidean coordinates about the geodesic, a Margulis region that is precisely invariant with multiplicity 1, and rescaling to a dominating point.

## 1. Your three options

**(1) Stable window, lemma W.** The lemma is true: Fix(nearGrp(z, Aⁱs)) is a decreasing chain of strata, so pigeonhole over ≤ (n+1)/2 windows gives a stable one. But the claim "Y a geodesic at a stable scale ⇒ no slow plane" is **false**.
- Counterexample: b rotates plane P₁ by θ₁ ≈ s and P₂ by θ₂ ≪ θ₁, with ŵ ∈ P₂ and e^d·θ₂ ≈ s.
- This is stable at every scale: every As-near-identity element fixes Y. Stability controls near-identity elements, while the obstruction comes from elements with small displacement at z but large rotation norm.

The "dim ≥ 2 ⇒ KM" half is correct when done as L3: take b of minimal norm in PtStab_Γ(Fix a), and apply CovolLB_j with j = dim Fix b (not dim Fix H), plus G3′, G4 and F9. The result is a gap, not a case split: every a ∈ Γ∖1 with dim Fix a ≥ 2 has rotation ≥ θ_*(V) := (c/V)^{1/α}, with α = n−1−(n−j)/2 > 0. With L3 in hand no window is needed.

**(2) Thickened torus-orbit tube.** Not needed. One ellipsoid-cylinder E_b inside the multiplicity-1 region suffices.

**(3) Kazhdan–Margulis on 2-planes through Y, or on Y × torus.**
- 2-planes: their stabilisers need not be lattices.
- ℝ × T^r: KM is false there, since the group is amenable.

The right tool is Dirichlet/Minkowski in torus coordinates, below.

## 2. The route

**Setup.** F := nearGrp(z,η), finite and nontrivial.
- By F13, each generator's fixed set has odd dimension ≥ 1.
- By L3, a generator with a larger fixed set is impossible, since its rotation is ≤ Cη < θ_*.
- So each generator fixes exactly a geodesic. By G1 they commute, so each preserves the others' axes, and near-identity rules out flips. Hence all axes coincide in one geodesic Y = Fix F.
- Conjugate Y to stdTG 1 m (F12, F14). Let P := PtStab_Γ(Y) (finite), N the setwise stabiliser of Y in Γ, N⁰ ⊂ N its part acting by translations on Y (index ≤ 2).
- **Gap clause (L3 + L2b):** every a ∈ P∖1 that is η₁-near-identity somewhere has Fix a = Y, where η₁ := min(η_Z, θ_J, θ_*(V))/C.

**A. Exact Euclidean model (L1).** Set u = fermiW(v,W), where fermiW(v,W) := (√(1+|W|²)·v, W), so W = nrmC u. For k = 1:
- The volume is exactly volH¹ ⊗ Lebesgue: tpart = √(1+|W|²)·tpart v, and the Jacobian in the one tangential coordinate cancels it.
- blk(h,R) acts by (v,W) ↦ (hv, RW).
- sinh²(D/2) = (1+|W|²)·sinh²(d(v,hv)/2) + |RW−W|²/4, exactly.

**B. Two-scale near-identity (L2).**
- If ‖R−1‖ ≤ c, |RW−W| ≤ c and 10c < η, then blk(1,R) is η-near-identity at u.
- Conversely, near-identity implies ‖R−1‖ ≤ 4η.
- Proof: a point within distance 1 is cosh a·X + sinh a·V. Its normal part is pŴ + q with |q| ≤ 1 and |p| ≤ √(1+|W|²).

**C. Margulis region with multiplicity 1 (L5).** Ω := {u : ∃ a ∈ P∖1, NearIdAt a u η₁}. Suppose u and γu are both in Ω, via a and a′.
- a and a″ := γ⁻¹a′γ are both η₁-near-identity at u.
- They generate a finite group (Zassenhaus, KM-C) with a fixed point p (KM-D), and they commute (G1).
- So a preserves Fix a″ = γ⁻¹Y, which passes through p.
- A flip of a geodesic through p moves a point at distance ½ from p by 1, which near-identity forbids. So a fixes γ⁻¹Y pointwise, γ⁻¹Y ⊆ Fix a = Y, and γ ∈ N.

This replaces G2/ConjCount entirely for k = 1. It works only because isometries of a geodesic that fix a point are ±1.

**D. Tube inequality (L6).** Ω = fermiW(ℍ¹ × U) with U invariant under the normal parts of N. Combining S7 (two cosets), F10 and L1:

  ℓ₀ · Leb(U) ≤ 2·|P|·V.

If N⁰ has no translation, the left side is ∞, a contradiction. Otherwise let g₀ ∈ N⁰ realise the minimal translation ℓ₀.

**E. Torus (L7).**
- A := ⟨p ∈ P : ‖R_p−1‖ ≤ θ_J⟩ is abelian (G1), with [P:A] ≤ J(m) by a covering of O(m), and F ⊆ A.
- Conjugation by g₀ permutes the ≤ m joint characters of A, so g := g₀^{m!} centralises A.
- A has no ±1 joint character: small generators force +1, which would give a fixed vector of F.
- Hence A and R_g lie in one maximal torus with planes P₁…P_r (r = m/2).
- L := ⟨g⟩A has translation T = m!·ℓ₀ and angles φ(c) ∈ (ℝ/2π)^r. Its displacement at W is monotone in each ρ_i(W) := |proj_{P_i} W|.

**F. Dominate and rescale (L10).** Choose W₀ with ρ_i(W₀) = max(ρ_i(W_z), ρ_*).
- The generator f gives λ₁(W₀) ≤ C_fη(1+√r·ρ_*) ≤ δ, where λ₁(W) := min over a ∈ A∖1 of |R_aW − W|.
- Set W″ := s·W₀ with s ≥ 1 and λ₁(W″) = δ exactly, attained by some b ∈ A.
- Then ‖R_b−1‖ ≤ δ/ρ_* ≤ c₀η₁ and |det(R_b−1)| ≤ δ^{2r}/∏ρ″ᵢ².
- So E_b := {|R_bW−W| ≤ c₀η₁} ⊆ U, and Leb(U) ≥ κ_m(c₀η₁)^m·∏ρ″ᵢ²/δ^{2r} (L8).

**G. Dirichlet pigeonhole (L9).** Use boxes of side α_i := δ/(2√r·ρ″ᵢ) and the points j·φ(g) + φ(a), for 0 ≤ j ≤ J := ⌊δ/(|W″|T)⌋ and a ∈ A.
- Two points in the same box with j = j′ would give an element of A∖1 with |R_aW″ − W″| < δ, contradicting λ₁ = δ.
- So j ≠ j′, and c := g^{j′−j}a⁻¹a′ has 0 < |τ_c| ≤ δ/|W″| and |(R_c−1)W″| < δ/2. It has infinite order and moves W″ by ≤ 2δ; by domination it moves z by ≤ 2δ.
- The pigeonhole needs T ≤ δ^{r+1}|A| / (|W″|·(8π√r)^r·∏ρ″ᵢ). By D and F this holds once ∏ρ″ᵢ ≥ C_n·V·|W″|·δ^{r−1}/η₁^m.
- Since |W″| ≤ √r·max ρ″ and ∏ρ″ ≥ max ρ″·ρ_*^{r−1}, it suffices that **ρ_*^{r−1} ≥ C_n√r·V·δ^{r−1}/η₁^m. This needs r ≥ 2.**

**Constants.**
- δ := 2C_f(1+√r)·η.
- ρ_* := max(1, δκ), with κ := max(1/(c₀η₁), (C_n√r·V/η₁^m)^{1/(r−1)}).
- η₀ := 1/(2C_f√r·κ). This also gives α_i ≤ 2π and |W″| ≥ 1.
- Consistency check for r = 1 (n = 3): decoupling the translation budget to δ_tr = C(1+V/η₁²)·δ recovers the lead's bound.

## 3. Lemmas

Helpers:
- `fermiW k m v W := WithLp.toLp 2 (Fin.append (fun i => √(1+‖W‖^2) * v i) (fun i => W i))`
- `rotN R := ‖(R : E m →L[ℝ] E m) - 1‖`

**L1 fermiW_chart** [certain now]
- (a) `MeasurePreserving (fun p : E 1 × E m => fermiW 1 m p.1 p.2) ((volH 1).prod volume) (volH (1+m))`
- (b) `blk k m h R • fermiW k m v W = fermiW k m (h • v) (R W)`
- (c) `Real.sinh (hdist u (blk k m h R • u) / 2) ^ 2 = (1 + ‖W‖^2) * Real.sinh (hdist v (h • v) / 2) ^ 2 + ‖R W - W‖^2 / 4`

**L2 nearId_blk** [certain now]. With u = fermiW 1 m v W:
- (a) `rotN R ≤ c → ‖R W - W‖ ≤ c → 10 * c < η → NearIdAt (blk 1 m 1 R) u η`
- (b) `NearIdAt (blk 1 m 1 R) u η → η ≤ 1 → rotN R ≤ 4 * η ∧ ‖R W - W‖ ≤ 2 * Real.sinh (η / 2)`

**L3 thinStrataGap** [certain given G1, G2, G3′, G4, F9, F10, F11, F12, F14, KM-J]

```
∀ n, ∃ c α : ℝ, 0 < c ∧ 0 < α ∧ ∀ k m (Λ : Subgroup (PO (k+m) 1)) D R, k + m = n → 2 ≤ k →
  IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH (k+m)) → blk k m 1 R ∈ Λ → R ≠ 1 →
  ∀ θ ∈ Set.Ioc 0 1, NearIdAt (blk k m 1 R) (coordEmb k m 0) θ → ENNReal.ofReal (c * θ ^ (-α)) ≤ volH (k+m) D
```

Sketch: b is the rotN-minimiser in P_X; Fix b has dimension j ≥ 2; then G3′ + G4 + CovolLB_j. The case vol(Y/res C) = ⊤ is a contradiction.

**L4 stratumOfF** [certain given L3, F13, G1, F12]. For all V there is η₀ > 0 such that for η ≤ η₀, if `nearGrp Λ z η ≠ ⊥` and `Finite (nearGrp Λ z η)`:
- (i) `∃ h, h • stdTG 1 m = {u | ∀ g ∈ nearGrp Λ z η, g • u = u}` (in set-image form);
- (ii) `∀ a ∈ Λ, a ≠ 1 → (∀ y ∈ h • stdTG 1 m, a • y = y) → (∃ u, NearIdAt a u η₁) → fixSet a = h • stdTG 1 m`.

**L5 marginInvariant** [certain given Zassenhaus, KM-C, KM-D, G1, L2]. With `Ω := {u | ∃ a ∈ Λ, a ≠ 1 ∧ (∀ y ∈ stdTG 1 m, a • y = y) ∧ NearIdAt a u η₁}`:
- `L4(ii) → η₁ ≤ η_Z → u ∈ Ω → γ ∈ Λ → γ • u ∈ Ω → γ ∈ SetStabStd 1 m`
- plus `nrmStd c '' (nrmC 1 m '' Ω) = nrmC 1 m '' Ω` for c ∈ Λ ⊓ SetStabStd.

**L6 tubeIneq1** [certain given L5, S7, F10, L1]. With `U := nrmC 1 m '' Ω`, `P := Λ ⊓ ker resStd`, N⁰ the translation part, and `IsFundamentalDomain (N⁰.map resStd) DY (volH 1)`:
- `volH 1 DY * volume U ≤ 2 * Nat.card P * volH (1+m) D`, and `volH 1 DY = ℓ₀`.

**L7 jordanTorus** [certain math; heavy linear algebra]
- `A := Subgroup.closure {p ∈ P | rotN (nrmStd p) ≤ θ_J}`, which is commutative, with `A.relindex P ≤ J m`.
- `∀ a ∈ A, g₀^(m !) * a = a * g₀^(m !)`.
- `∃ e : OrthonormalBasis (Fin (m/2) × Fin 2) ℝ (E m), ∃ φ`, such that every `nrmStd c` for c ∈ ⟨g₀^(m !)⟩ ⊔ A rotates `span {e (i,0), e (i,1)}` by `φ c i`.
- Hypothesis: A has no nonzero common fixed vector.
- Proof: complex joint eigenvectors; the character permutation has order dividing m!.

**L8 ellipsoidVol** [certain now, via `addHaar_preimage_linearMap`]
- `volume {W | ‖R W - W‖ ≤ c} = ENNReal.ofReal (c ^ m / |LinearMap.det (R - 1)|) * volume (closedBall 0 1)`
- In torus form: `|det (R - 1)| = ∏ i, (2 * sin (φ i / 2)) ^ 2`.

**L9 dirichletBox** [certain now, pure combinatorics]

```
∀ (A : AddSubgroup (Fin r → AddCircle (2*π))) [Finite A] ψ (α : Fin r → ℝ) J,
 (∀ i, 0 < α i ∧ α i ≤ 2*π) → (∀ a ∈ A, (∀ i, ‖a i‖ < α i) → a = 0) →
 ∏ i, ⌈2*π / α i⌉₊ < (J+1) * Nat.card A → ∃ j, 1 ≤ j ∧ j ≤ J ∧ ∃ a ∈ A, ∀ i, ‖j • ψ i + a i‖ < α i
```

**L10 rescaledPoint** [certain now]. Given ρ̃ᵢ := max(ρᵢ, ρ_*) and some f ∈ A∖0 with `∑ ρ̃ᵢ²·4sin²(fᵢ/2) ≤ δ²`, there exist s ≥ 1 and b ∈ A∖0 with `∑ (sρ̃ᵢ)²·4sin²(bᵢ/2) = δ²`, and `δ² ≤ ∑ (sρ̃ᵢ)²·4sin²(aᵢ/2)` for all a ∈ A∖0.

**L11 geodStratum** [assembly of L1–L10, as in §2]

```
4 ≤ m → Even m → ∃ C > 0, ∀ V, ∃ η₀ > 0, ∀ η ∈ Ioc 0 η₀, ∀ Λ D z, IsDiscrete ↑Λ →
 IsFundamentalDomain Λ D (volH (1+m)) → volH _ D ≤ ofReal V → nearGrp Λ z η ≠ ⊥ → Finite (nearGrp Λ z η) →
 ∃ γ ∈ Λ, ¬ IsOfFinOrder γ ∧ hdist z (γ • z) ≤ C * η
```

**L12 gapA_odd** [assembly: S1 FrameThinFar; infinite F handled as in gapA_even; finite F by L11 with η := min(ε/C, η₀(V))]
- `Odd n → 5 ≤ n → HypLattice Γ → ∀ ε > 0, ∃ K, IsCompact K ∧ ∀ u, (∀ γ : Γ, γ • u ∉ K) → ∃ g : Γ, ¬ IsOfFinOrder g ∧ hdist u (g • u) < ε`

## 4. What is certain, what is not needed, what remains

**Certain now:** L1, L2, L8, L9, L10. Also L5 and L6 once Zassenhaus, KM-C, KM-D, G1, S7 and F10 exist.

**Certain but heavy:** L7 (joint normal form of a commuting orthogonal family, and the m! power), and L3, whose inputs are the same as T-even's.

**Not needed for k = 1:**
- lemma W and the stable window;
- G2/ConjCount and Weyl counting;
- the round-tube G3′;
- counting elements that are short at z;
- successive minima, Minkowski II, lattice fundamental domains;
- torus-orbit tubes;
- the slow-plane case analysis;
- a D(1+V) factor in the final bound.

**Remaining gap:** none mathematically. Two things should be checked before dispatch:
- **L7** is the main linear-algebra risk. Look for Mathlib's joint eigenspaces for commuting normal operators; otherwise derive them from the commuting symmetric/skew parts.
- **L3 depends on odd strata ≥ 3.** Confirm that KM-J/CovolLB is stated for all j ≥ 2, including the odd j ≥ 3 that L3 needs, and that G4's torus packing reuses L7.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem ellipsoidVol (m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) (hR : ∀ w, R w = w → w = 0) (c : ℝ) (hc : 0 ≤ c) :
    volume {W : E m | ‖R W - W‖ ≤ c} =
      ENNReal.ofReal (c ^ m / |LinearMap.det ((R.toLinearEquiv : E m →ₗ[ℝ] E m) - LinearMap.id)|) *
        volume (Metric.closedBall (0 : E m) 1) := by
  -- `R - 1` is injective, hence (finite dimension) has nonzero determinant
  have hker : ((R.toLinearEquiv : E m →ₗ[ℝ] E m) - (LinearMap.id : E m →ₗ[ℝ] E m)).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hx' : R x - x = 0 := by simpa using hx
    exact hR x (sub_eq_zero.mp hx')
  have hdet : LinearMap.det
      ((R.toLinearEquiv : E m →ₗ[ℝ] E m) - (LinearMap.id : E m →ₗ[ℝ] E m)) ≠ 0 :=
    fun h => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) hker
  -- the set is the preimage of a Euclidean ball under the (invertible) linear map `R - 1`
  have hset : {W : E m | ‖R W - W‖ ≤ c} =
      ((R.toLinearEquiv : E m →ₗ[ℝ] E m) - (LinearMap.id : E m →ₗ[ℝ] E m)) ⁻¹'
        Metric.closedBall (0 : E m) c := by
    ext W
    simp [LinearMap.sub_apply, LinearIsometryEquiv.coe_toLinearEquiv, Metric.mem_closedBall,
      dist_eq_norm]
  -- Haar measure scales by the determinant under a linear map, and balls scale by `c ^ m`
  have key : ∀ (g : E m →ₗ[ℝ] E m), LinearMap.det g ≠ 0 →
      volume (g ⁻¹' Metric.closedBall (0 : E m) c) =
        ENNReal.ofReal (c ^ m / |LinearMap.det g|) * volume (Metric.closedBall (0 : E m) 1) := by
    intro g hg
    have hscal : ENNReal.ofReal |LinearMap.det g|⁻¹ * ENNReal.ofReal (c ^ m) =
        ENNReal.ofReal (c ^ m / |LinearMap.det g|) := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (abs_nonneg _)), div_eq_mul_inv, mul_comm]
    rw [Measure.addHaar_preimage_linearMap volume hg,
      Measure.addHaar_closedBall' volume (0 : E m) hc, finrank_euclideanSpace, Fintype.card_fin,
      abs_inv, ← mul_assoc, hscal]
  rw [hset, key _ hdet]

end Work.Mostow
