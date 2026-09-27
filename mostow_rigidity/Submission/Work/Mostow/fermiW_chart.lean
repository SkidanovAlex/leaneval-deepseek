import Mathlib
import Submission.Mostow.GeodDefs
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.fermi_inv
import Submission.Work.Mostow.cosh_hdist_fermi
import Submission.Work.Mostow.VolDefs
import Submission.Work.Mostow.areaFormula
import Submission.Work.Mostow.measurePreserving_prodeMap

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
open scoped ENNReal

noncomputable section

/-! ## The two coordinate systems `fermi` and `fermiW`

`fermiW k m v W` is `fermi k m v w` for the unique `w` with `sinhc ‖w‖ • w = W`; the maps
`phiOf` (expansion) and `wOf` (shrink) implement this dictionary. -/

/-- The "sinhc expansion" `w ↦ sinhc ‖w‖ • w`, whose image is the normal coordinate `W`. -/
def phiOf {m : ℕ} (w : E m) : E m := sinhc ‖w‖ • w

/-- The "arsinh shrink" `W ↦ (arsinh ‖W‖ / ‖W‖) • W`, a section of `phiOf` (junk-free at `0`). -/
def wOf {m : ℕ} (W : E m) : E m := (Real.arsinh ‖W‖ / ‖W‖) • W

lemma sinhc_pos_fermiW_chart (s : ℝ) : 0 < sinhc s := by
  rw [sinhc]
  by_cases h : s = 0
  · simp [h]
  · simp only [h, ↓reduceIte]
    by_cases hs : 0 < s
    · exact div_pos (Real.sinh_pos_iff.mpr hs) hs
    · have hs' : s < 0 := lt_of_le_of_ne (not_lt.mp hs) h
      exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.mpr hs') hs'

lemma sinhc_nonneg (s : ℝ) : 0 ≤ sinhc s := le_of_lt (sinhc_pos_fermiW_chart s)

lemma sinhc_mul_self (s : ℝ) : sinhc s * s = Real.sinh s := by
  rw [sinhc]
  by_cases h : s = 0
  · simp [h]
  · rw [ite_eq_right h, div_mul_cancel₀ _ h]

lemma sinhc_mul_norm {m : ℕ} (w : E m) : sinhc ‖w‖ * ‖w‖ = Real.sinh ‖w‖ :=
  sinhc_mul_self ‖w‖

lemma norm_phiOf {m : ℕ} (w : E m) : ‖phiOf w‖ = Real.sinh ‖w‖ := by
  rw [phiOf, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sinhc_nonneg ‖w‖), sinhc_mul_norm]

lemma norm_wOf {m : ℕ} (W : E m) : ‖wOf W‖ = Real.arsinh ‖W‖ := by
  rw [wOf, norm_smul, Real.norm_eq_abs]
  by_cases h : ‖W‖ = 0
  · simp [h]
  · rw [abs_of_nonneg, div_mul_cancel₀ _ h]
    exact div_nonneg (Real.arsinh_nonneg_iff.mpr (norm_nonneg W)) (norm_nonneg W)

lemma phiOf_wOf {m : ℕ} (W : E m) : phiOf (wOf W) = W := by
  have h1 : ‖wOf W‖ = Real.arsinh ‖W‖ := norm_wOf W
  rw [phiOf, h1, wOf, smul_smul]
  by_cases h : W = 0
  · simp [h]
  · have hs : sinhc (Real.arsinh ‖W‖) * (Real.arsinh ‖W‖ / ‖W‖) = 1 := by
      rw [← mul_div_assoc, sinhc_mul_self, Real.sinh_arsinh,
        div_self (norm_ne_zero_iff.mpr h)]
    rw [hs, one_smul]

lemma wOf_phiOf {m : ℕ} (w : E m) : wOf (phiOf w) = w := by
  have h1 : ‖phiOf w‖ = Real.sinh ‖w‖ := norm_phiOf w
  rw [wOf, h1]
  by_cases h : w = 0
  · simp [h]
  · have hw : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have hsinh : Real.sinh ‖w‖ ≠ 0 := Real.sinh_ne_zero.mpr hw
    rw [Real.arsinh_sinh, phiOf, smul_smul]
    have hcoef : ‖w‖ / Real.sinh ‖w‖ * sinhc ‖w‖ = 1 := by
      rw [sinhc, ite_eq_right hw]
      field_simp
    rw [hcoef, one_smul]

lemma phiOf_injective {m : ℕ} : Function.Injective (@phiOf m) :=
  fun w w' h => by rw [← wOf_phiOf w, h, wOf_phiOf w']

lemma phiOf_smul {m : ℕ} (R : E m ≃ₗᵢ[ℝ] E m) (w : E m) : phiOf (R w) = R (phiOf w) := by
  rw [phiOf, phiOf, R.norm_map, map_smul]

/-! ## Dictionary between `fermi` and `fermiW` through `prodeMap` -/

lemma fermi_eq_prodeMap (k m : ℕ) (v : E k) (w : E m) :
    fermi k m v w = prodeMap k m (Real.cosh ‖w‖ • v, phiOf w) := rfl

lemma fermiW_eq_prodeMap (k m : ℕ) (v : E k) (W : E m) :
    fermiW k m v W = prodeMap k m (tpart W • v, W) := by
  rfl

lemma tpart_phiOf {m : ℕ} (w : E m) : tpart (phiOf w) = Real.cosh ‖w‖ := by
  rw [tpart]
  have h : 1 + ‖phiOf w‖ ^ 2 = Real.cosh ‖w‖ ^ 2 := by
    rw [norm_phiOf]
    have := Real.cosh_sq_sub_sinh_sq ‖w‖
    linarith
  rw [h, Real.sqrt_sq (Real.cosh_pos _).le]

lemma fermiW_eq_fermi (k m : ℕ) (v : E k) (W : E m) :
    fermiW k m v W = fermi k m v (wOf W) := by
  rw [fermiW_eq_prodeMap, fermi_eq_prodeMap]
  congr 1
  refine Prod.ext ?_ ?_
  · have h : tpart W = Real.cosh ‖wOf W‖ := by
      rw [norm_wOf, Real.cosh_arsinh]
      simp only [tpart]
    rw [h]
  · exact (phiOf_wOf W).symm

lemma fermi_eq_fermiW (k m : ℕ) (v : E k) (w : E m) :
    fermi k m v w = fermiW k m v (phiOf w) := by
  rw [fermi_eq_prodeMap, fermiW_eq_prodeMap]
  congr 1
  exact Prod.ext (by rw [tpart_phiOf]) rfl

lemma tpart_fermiW (k m : ℕ) (v : E k) (W : E m) :
    tpart (fermiW k m v W) = tpart W * tpart v := by
  rw [fermiW_eq_fermi, (fermi_inv k m).2.2 v (wOf W), norm_wOf, Real.cosh_arsinh]
  rfl

/-! ## (b) and (c): the block action in `(v,W)` coordinates -/

theorem blk_smul_fermiW (m : ℕ) (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (h : PO 1 1) (R : E m ≃ₗᵢ[ℝ] E m) (v : E 1) (W : E m) :
    blk 1 m h R • fermiW 1 m v W = fermiW 1 m (h • v) (R W) := by
  calc blk 1 m h R • fermiW 1 m v W
      = blk 1 m h R • fermi 1 m v (wOf W) := by rw [fermiW_eq_fermi]
    _ = fermi 1 m (h • v) (R (wOf W)) := blk_smul_fermi 1 m hA1 hI1 hA hI h R v (wOf W)
    _ = fermiW 1 m (h • v) (phiOf (R (wOf W))) := by rw [fermi_eq_fermiW]
    _ = fermiW 1 m (h • v) (R W) := by rw [phiOf_smul, phiOf_wOf]

/-- `2 * sinh (x/2)^2 = cosh x - 1`. -/
lemma two_mul_sinh_sq_half (x : ℝ) : 2 * Real.sinh (x / 2) ^ 2 = Real.cosh x - 1 := by
  have h := Real.cosh_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  have h2 := Real.cosh_sq (x / 2)
  linarith

/-- (c): the exact squared-displacement identity in `(v,W)` coordinates. -/
theorem disp_fermiW (m : ℕ) (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m))
    (h : PO 1 1) (R : E m ≃ₗᵢ[ℝ] E m) (v : E 1) (W : E m) :
    Real.sinh (hdist (fermiW 1 m v W) (blk 1 m h R • fermiW 1 m v W) / 2) ^ 2 =
      (1 + ‖W‖ ^ 2) * Real.sinh (hdist v (h • v) / 2) ^ 2 + ‖R W - W‖ ^ 2 / 4 := by
  have hblk : blk 1 m h R • fermiW 1 m v W = fermi 1 m (h • v) (R (wOf W)) := by
    rw [fermiW_eq_fermi, blk_smul_fermi 1 m hA1 hI1 hA hI h R v (wOf W)]
  rw [hblk, fermiW_eq_fermi]
  have hcoshD : Real.cosh (hdist (fermi 1 m v (wOf W)) (fermi 1 m (h • v) (R (wOf W))))
      = Real.cosh ‖wOf W‖ ^ 2 * Real.cosh (hdist v (h • v)) -
        sinhc ‖wOf W‖ ^ 2 * inner ℝ (wOf W) (R (wOf W)) := by
    rw [cosh_hdist_fermi 1 m v (h • v) (wOf W) (R (wOf W)), R.norm_map]
    ring
  have hcoshW : Real.cosh ‖wOf W‖ ^ 2 = 1 + ‖W‖ ^ 2 := by
    rw [norm_wOf, Real.cosh_arsinh, Real.sq_sqrt (by positivity)]
  have hsinhW : Real.sinh ‖wOf W‖ = ‖W‖ := by
    rw [norm_wOf, Real.sinh_arsinh]
  have hRW : ‖R W - W‖ ^ 2 = sinhc ‖wOf W‖ ^ 2 * ‖R (wOf W) - wOf W‖ ^ 2 := by
    have h1 : R W - W = sinhc ‖wOf W‖ • (R (wOf W) - wOf W) := by
      have hW : W = sinhc ‖wOf W‖ • wOf W := (phiOf_wOf W).symm
      conv_lhs => rw [hW]
      rw [map_smul, smul_sub]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sinhc_nonneg _), mul_pow]
  have hj : ‖R (wOf W) - wOf W‖ ^ 2 = 2 * ‖wOf W‖ ^ 2 - 2 * inner ℝ (wOf W) (R (wOf W)) := by
    rw [norm_sub_sq_real, R.norm_map, real_inner_comm (R (wOf W)) (wOf W)]
    ring
  have hs : sinhc ‖wOf W‖ ^ 2 * ‖wOf W‖ ^ 2 = Real.sinh ‖wOf W‖ ^ 2 := by
    rw [← mul_pow, sinhc_mul_norm]
  have key : sinhc ‖wOf W‖ ^ 2 * ‖wOf W‖ ^ 2 = ‖W‖ ^ 2 := by rw [hs, hsinhW]
  have hmain : Real.cosh (hdist (fermi 1 m v (wOf W)) (fermi 1 m (h • v) (R (wOf W)))) - 1
      = (1 + ‖W‖ ^ 2) * (Real.cosh (hdist v (h • v)) - 1) + ‖R W - W‖ ^ 2 / 2 := by
    rw [hcoshD, hcoshW, hRW, hj]
    linear_combination (-1) * key
  have hLHS : Real.sinh (hdist (fermi 1 m v (wOf W)) (fermi 1 m (h • v) (R (wOf W))) / 2) ^ 2
      = (Real.cosh (hdist (fermi 1 m v (wOf W)) (fermi 1 m (h • v) (R (wOf W)))) - 1) / 2 := by
    linarith [two_mul_sinh_sq_half
      (hdist (fermi 1 m v (wOf W)) (fermi 1 m (h • v) (R (wOf W))))]
  have hRHS : Real.sinh (hdist v (h • v) / 2) ^ 2
      = (Real.cosh (hdist v (h • v)) - 1) / 2 := by
    linarith [two_mul_sinh_sq_half (hdist v (h • v))]
  rw [hLHS, hRHS]
  have h2 : (1 + ‖W‖ ^ 2) * ((Real.cosh (hdist v (h • v)) - 1) / 2) + ‖R W - W‖ ^ 2 / 4
      = (Real.cosh (hdist (fermi 1 m v (wOf W)) (fermi 1 m (h • v) (R (wOf W)))) - 1) / 2 := by
    rw [show (Real.cosh (hdist (fermi 1 m v (wOf W)) (fermi 1 m (h • v) (R (wOf W)))) - 1) / 2
        = ((1 + ‖W‖ ^ 2) * (Real.cosh (hdist v (h • v)) - 1) + ‖R W - W‖ ^ 2 / 2) / 2 from by
      rw [hmain]]
    ring
  exact h2.symm

/-! ## (a) The measure-preserving statement

`fermiW 1 m = prodeMap 1 m ∘ hmapPhase`, where `hmapPhase (v,W) = (tpart W • v, W)`.  We compute
the pushforward of `volH 1 ⊗ volume` under `hmapPhase` by Tonelli together with the exact
one-dimensional scaling law for `volH 1`, and then push forward along `prodeMap`, which preserves
Lebesgue measure (`Work.Mostow.measurePreserving_prodeMap`). -/

/-- The "linear part" of `fermiW`: `(v,W) ↦ (√(1+‖W‖²)·v, W)`. -/
def hmapPhase {m : ℕ} (p : E 1 × E m) : E 1 × E m := (tpart p.2 • p.1, p.2)

lemma measurable_prodeMap_one (m : ℕ) : Measurable (prodeMap 1 m) :=
  (measurePreserving_prodeMap 1 m).measurable

lemma measurable_hmapPhase {m : ℕ} : Measurable (hmapPhase (m := m)) :=
  Measurable.prod ((continuous_tpart_VolDefs.measurable.comp measurable_snd).smul measurable_fst)
    measurable_snd

/-- `u ↦ (u, W)` is measurable. -/
lemma measurable_prodMk_fst {m : ℕ} (W : E m) : Measurable (fun u : E 1 => (u, W)) :=
  (measurableEmbedding_prod_mk_right W).measurable

/-- Lebesgue measure on `E 1` under the scaling `x ↦ a • x` (`a > 0`). -/
lemma lintegral_comp_smul_volume {a : ℝ} (ha : 0 < a) {G : E 1 → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ x, G (a • x) ∂(volume : Measure (E 1))
      = ENNReal.ofReal a⁻¹ * ∫⁻ x, G x ∂(volume : Measure (E 1)) := by
  have hfr : Module.finrank ℝ (E 1) = 1 := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have hmap : Measure.map (fun x : E 1 => a • x) (volume : Measure (E 1))
      = ENNReal.ofReal a⁻¹ • (volume : Measure (E 1)) := by
    have h := Measure.map_addHaar_smul (μ := (volume : Measure (E 1))) (r := a) ha.ne'
    rw [hfr, pow_one, abs_of_pos (inv_pos.mpr ha)] at h
    exact h
  calc ∫⁻ x, G (a • x) ∂(volume : Measure (E 1))
      = ∫⁻ x, G x ∂(Measure.map (fun x : E 1 => a • x) (volume : Measure (E 1))) :=
        (lintegral_map hG (measurable_const_smul a)).symm
    _ = ∫⁻ x, G x ∂(ENNReal.ofReal a⁻¹ • (volume : Measure (E 1))) := by rw [hmap]
    _ = ENNReal.ofReal a⁻¹ * ∫⁻ x, G x ∂(volume : Measure (E 1)) := by
        rw [lintegral_smul_measure, smul_eq_mul]

/-- `a⁻¹ * (√(1 + (a⁻¹)²r²))⁻¹ = (√(a² + r²))⁻¹` for `a > 0`. -/
lemma inv_mul_inv_sqrt (a r : ℝ) (ha : 0 < a) :
    a⁻¹ * (Real.sqrt (1 + (a⁻¹) ^ 2 * r ^ 2))⁻¹ = (Real.sqrt (a ^ 2 + r ^ 2))⁻¹ := by
  have halg : a ^ 2 * (1 + (a⁻¹) ^ 2 * r ^ 2) = a ^ 2 + r ^ 2 := by
    have ha' : a ≠ 0 := ha.ne'
    rw [inv_pow]
    field_simp
    try ring
  have hkey : Real.sqrt (a ^ 2 + r ^ 2) = a * Real.sqrt (1 + (a⁻¹) ^ 2 * r ^ 2) := by
    have hsq : (Real.sqrt (a ^ 2 + r ^ 2)) ^ 2
        = (a * Real.sqrt (1 + (a⁻¹) ^ 2 * r ^ 2)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by positivity), halg]
    have hpos1 : 0 < Real.sqrt (a ^ 2 + r ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hpos2 : 0 < a * Real.sqrt (1 + (a⁻¹) ^ 2 * r ^ 2) :=
      mul_pos ha (Real.sqrt_pos.mpr (by positivity))
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · exact absurd h (fun hh => by linarith)
  rw [hkey, mul_inv]

/-- The density factor produced by the scaling `x ↦ a • x` in the first `E 1`-coordinate. -/
lemma hdens_coeff {a : ℝ} (ha : 0 < a) (u : E 1) :
    ENNReal.ofReal a⁻¹ * hdens (a⁻¹ • u)
      = ENNReal.ofReal (1 / Real.sqrt (a ^ 2 + ‖u‖ ^ 2)) := by
  rw [hdens, tpart, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha), mul_pow,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ a⁻¹), one_div,
    inv_mul_inv_sqrt a ‖u‖ ha]

/-- One-dimensional scaling law for `volH 1`: `∫⁻ v, f (a • v) ∂volH 1 = ∫⁻ u, f u / √(a²+‖u‖²)`. -/
lemma lintegral_comp_smul_volH_one {a : ℝ} (ha : 0 < a) (f : E 1 → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ v, f (a • v) ∂(volH 1)
      = ∫⁻ u, f u * ENNReal.ofReal (1 / Real.sqrt (a ^ 2 + ‖u‖ ^ 2))
          ∂(volume : Measure (E 1)) := by
  set G : E 1 → ℝ≥0∞ := fun y => f y * hdens (a⁻¹ • y) with hG_def
  have hG : Measurable G := by
    rw [hG_def]
    exact hf.mul (measurable_hdens.comp (measurable_const_smul a⁻¹))
  have h1 : ∫⁻ v, f (a • v) ∂(volH 1)
      = ∫⁻ v, hdens v * f (a • v) ∂(volume : Measure (E 1)) := by
    rw [volH_def]
    exact lintegral_withDensity_eq_lintegral_mul (volume : Measure (E 1)) measurable_hdens
      (hf.comp (measurable_const_smul a))
  have h2 : ∫⁻ v, hdens v * f (a • v) ∂(volume : Measure (E 1))
      = ∫⁻ v, G (a • v) ∂(volume : Measure (E 1)) := by
    refine lintegral_congr fun v => ?_
    simp only [hG_def]
    change hdens v * f (a • v) = f (a • v) * hdens (a⁻¹ • (a • v))
    rw [show a⁻¹ • (a • v) = v from by rw [smul_smul, inv_mul_cancel₀ ha.ne', one_smul],
      mul_comm]
  have h3 : ∫⁻ v, G (a • v) ∂(volume : Measure (E 1))
      = ENNReal.ofReal a⁻¹ * ∫⁻ y, G y ∂(volume : Measure (E 1)) :=
    lintegral_comp_smul_volume (G := G) ha hG
  have h4 : ENNReal.ofReal a⁻¹ * ∫⁻ y, G y ∂(volume : Measure (E 1))
      = ∫⁻ u, f u * ENNReal.ofReal (1 / Real.sqrt (a ^ 2 + ‖u‖ ^ 2))
          ∂(volume : Measure (E 1)) := by
    rw [← lintegral_const_mul (ENNReal.ofReal a⁻¹) hG]
    refine lintegral_congr fun u => ?_
    simp only [hG_def]
    rw [← mul_assoc, mul_comm (ENNReal.ofReal a⁻¹) (f u), mul_assoc, hdens_coeff ha u]
  rw [h1, h2, h3, h4]

lemma norm_sq_prodeMap_one (m : ℕ) (u : E 1) (W : E m) :
    ‖prodeMap 1 m (u, W)‖ ^ 2 = ‖u‖ ^ 2 + ‖W‖ ^ 2 := by
  rw [show prodeMap 1 m (u, W) = WithLp.toLp 2 (Fin.append (u : Fin 1 → ℝ) (W : Fin m → ℝ))
      from rfl, EuclideanSpace.real_norm_sq_eq]
  change (∑ i : Fin (1 + m), (Fin.append (u : Fin 1 → ℝ) (W : Fin m → ℝ) i) ^ 2)
      = ‖u‖ ^ 2 + ‖W‖ ^ 2
  have hA : (∑ i : Fin 1,
        (Fin.append (u : Fin 1 → ℝ) (W : Fin m → ℝ) (Fin.castAdd m i)) ^ 2) = ‖u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_left]
  have hB : (∑ i : Fin m,
        (Fin.append (u : Fin 1 → ℝ) (W : Fin m → ℝ) (Fin.natAdd 1 i)) ^ 2) = ‖W‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by rw [Fin.append_right]
  rw [Fin.sum_univ_add, hA, hB]

lemma tpart_prodeMap_one (m : ℕ) (u : E 1) (W : E m) :
    tpart (prodeMap 1 m (u, W)) = Real.sqrt (tpart W ^ 2 + ‖u‖ ^ 2) := by
  rw [tpart, norm_sq_prodeMap_one, tpart, Real.sq_sqrt (by positivity)]
  congr 1
  ring

lemma hdens_one_add_prodeMap (m : ℕ) (u : E 1) (W : E m) :
    hdens (prodeMap 1 m (u, W))
      = ENNReal.ofReal (1 / Real.sqrt (tpart W ^ 2 + ‖u‖ ^ 2)) := by
  rw [hdens, tpart_prodeMap_one, one_div]

/-- Pushforward of `volH 1 ⊗ volume` under the linear part `(v,W) ↦ (√(1+‖W‖²)·v, W)`. -/
theorem hmap_pushforward (m : ℕ) :
    Measure.map (hmapPhase (m := m)) ((volH 1).prod (volume : Measure (E m))) =
      ((volume : Measure (E 1)).prod (volume : Measure (E m))).withDensity
        (fun p => hdens (prodeMap 1 m p)) := by
  have hdens_meas : Measurable (fun p : E 1 × E m => hdens (prodeMap 1 m p)) :=
    measurable_hdens.comp (measurable_prodeMap_one m)
  have hdens_fst : Measurable (fun z : E 1 × E m => hdens z.1) :=
    measurable_hdens.comp measurable_fst
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hmap_meas : Measurable (fun p : E 1 × E m => f (hmapPhase p)) :=
    hf.comp measurable_hmapPhase
  have hL : ∫⁻ p, f p
        ∂(Measure.map (hmapPhase (m := m)) ((volH 1).prod (volume : Measure (E m))))
      = ∫⁻ W, ∫⁻ u, f (u, W) * ENNReal.ofReal (1 / Real.sqrt (tpart W ^ 2 + ‖u‖ ^ 2))
          ∂(volume : Measure (E 1)) ∂(volume : Measure (E m)) := by
    have h1 : ∫⁻ p, f p
          ∂(Measure.map (hmapPhase (m := m)) ((volH 1).prod (volume : Measure (E m))))
        = ∫⁻ p, f (hmapPhase p) ∂((volH 1).prod (volume : Measure (E m))) :=
      lintegral_map hf measurable_hmapPhase
    have h2 : ∫⁻ p, f (hmapPhase p) ∂((volH 1).prod (volume : Measure (E m)))
        = ∫⁻ p, f (hmapPhase p)
            ∂(((volume : Measure (E 1)).prod (volume : Measure (E m))).withDensity
              (fun z : E 1 × E m => hdens z.1)) := by
      rw [volH_def, MeasureTheory.prod_withDensity_left (μ := (volume : Measure (E 1)))
        (ν := (volume : Measure (E m))) measurable_hdens]
    have h3 : ∫⁻ p, f (hmapPhase p)
            ∂(((volume : Measure (E 1)).prod (volume : Measure (E m))).withDensity
              (fun z : E 1 × E m => hdens z.1))
        = ∫⁻ p, hdens p.1 * f (hmapPhase p)
            ∂((volume : Measure (E 1)).prod (volume : Measure (E m))) :=
      lintegral_withDensity_eq_lintegral_mul _ hdens_fst hmap_meas
    have h4 : ∫⁻ p, hdens p.1 * f (hmapPhase p)
            ∂((volume : Measure (E 1)).prod (volume : Measure (E m)))
        = ∫⁻ W, ∫⁻ v, hdens v * f (hmapPhase (v, W))
            ∂(volume : Measure (E 1)) ∂(volume : Measure (E m)) :=
      lintegral_prod_symm' _ (hdens_fst.mul hmap_meas)
    have h5 : ∫⁻ W, ∫⁻ v, hdens v * f (hmapPhase (v, W))
            ∂(volume : Measure (E 1)) ∂(volume : Measure (E m))
        = ∫⁻ W, ∫⁻ u, f (u, W) * ENNReal.ofReal (1 / Real.sqrt (tpart W ^ 2 + ‖u‖ ^ 2))
            ∂(volume : Measure (E 1)) ∂(volume : Measure (E m)) := by
      refine lintegral_congr fun W => ?_
      have hsub : Measurable (fun u : E 1 => f (u, W)) := hf.comp (measurable_prodMk_fst W)
      have ha : ∫⁻ v, hdens v * f (hmapPhase (v, W)) ∂(volume : Measure (E 1))
          = ∫⁻ v, f (hmapPhase (v, W)) ∂(volH 1) :=
        (lintegral_withDensity_eq_lintegral_mul (volume : Measure (E 1)) measurable_hdens
          (hf.comp (measurable_hmapPhase.comp (measurable_prodMk_fst W)))).symm
      have hb : ∫⁻ v, f (hmapPhase (v, W)) ∂(volH 1)
          = ∫⁻ v, (fun u : E 1 => f (u, W)) (tpart W • v) ∂(volH 1) := by
        refine lintegral_congr fun v => ?_
        rfl
      have hc : ∫⁻ v, (fun u : E 1 => f (u, W)) (tpart W • v) ∂(volH 1)
          = ∫⁻ u, f (u, W) * ENNReal.ofReal (1 / Real.sqrt (tpart W ^ 2 + ‖u‖ ^ 2))
              ∂(volume : Measure (E 1)) :=
        lintegral_comp_smul_volH_one (tpart_pos W) (fun u : E 1 => f (u, W)) hsub
      rw [ha, hb, hc]
    rw [h1, h2, h3, h4, h5]
  have hR : ∫⁻ p, f p ∂(((volume : Measure (E 1)).prod (volume : Measure (E m))).withDensity
        (fun p => hdens (prodeMap 1 m p)))
      = ∫⁻ W, ∫⁻ u, f (u, W) * ENNReal.ofReal (1 / Real.sqrt (tpart W ^ 2 + ‖u‖ ^ 2))
          ∂(volume : Measure (E 1)) ∂(volume : Measure (E m)) := by
    have h1 : ∫⁻ p, f p ∂(((volume : Measure (E 1)).prod (volume : Measure (E m))).withDensity
          (fun p => hdens (prodeMap 1 m p)))
        = ∫⁻ p, hdens (prodeMap 1 m p) * f p
            ∂((volume : Measure (E 1)).prod (volume : Measure (E m))) :=
      lintegral_withDensity_eq_lintegral_mul _ hdens_meas hf
    have h2 : ∫⁻ p, hdens (prodeMap 1 m p) * f p
            ∂((volume : Measure (E 1)).prod (volume : Measure (E m)))
        = ∫⁻ W, ∫⁻ u, hdens (prodeMap 1 m (u, W)) * f (u, W)
            ∂(volume : Measure (E 1)) ∂(volume : Measure (E m)) :=
      lintegral_prod_symm' _ (hdens_meas.mul hf)
    have h3 : ∫⁻ W, ∫⁻ u, hdens (prodeMap 1 m (u, W)) * f (u, W)
            ∂(volume : Measure (E 1)) ∂(volume : Measure (E m))
        = ∫⁻ W, ∫⁻ u, f (u, W) * ENNReal.ofReal (1 / Real.sqrt (tpart W ^ 2 + ‖u‖ ^ 2))
            ∂(volume : Measure (E 1)) ∂(volume : Measure (E m)) := by
      refine lintegral_congr fun W => ?_
      refine lintegral_congr fun u => ?_
      rw [hdens_one_add_prodeMap, mul_comm]
    rw [h1, h2, h3]
  rw [hL, hR]

theorem fermiW_measurePreserving (m : ℕ) :
    MeasurePreserving (fun p : E 1 × E m => fermiW 1 m p.1 p.2) ((volH 1).prod volume)
      (volH (1 + m)) := by
  have hF : (fun p : E 1 × E m => fermiW 1 m p.1 p.2) = prodeMap 1 m ∘ hmapPhase (m := m) := by
    funext p
    rw [Function.comp_apply]
    rfl
  have hmeas : Measurable (fun p : E 1 × E m => fermiW 1 m p.1 p.2) := by
    rw [hF]
    exact (measurable_prodeMap_one m).comp measurable_hmapPhase
  refine MeasurePreserving.mk hmeas ?_
  rw [hF, ← Measure.map_map (measurable_prodeMap_one m) measurable_hmapPhase,
    hmap_pushforward m]
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply (measurable_prodeMap_one m) hB,
    withDensity_apply _ (hB.preimage (measurable_prodeMap_one m)), volHApply (1 + m) hB]
  exact (measurePreserving_prodeMap 1 m).setLIntegral_comp_preimage hB (measurable_hdens)

end

theorem fermiW_chart (m : ℕ) (hA1 : POActionProp 1) (hI1 : HypIsometryProp 1)
    (hA : POActionProp (1 + m)) (hI : HypIsometryProp (1 + m)) :
    MeasurePreserving (fun p : E 1 × E m => fermiW 1 m p.1 p.2) ((volH 1).prod volume) (volH (1 + m)) ∧
    (∀ (h : PO 1 1) (R : E m ≃ₗᵢ[ℝ] E m) (v : E 1) (W : E m),
      blk 1 m h R • fermiW 1 m v W = fermiW 1 m (h • v) (R W)) ∧
    ∀ (h : PO 1 1) (R : E m ≃ₗᵢ[ℝ] E m) (v : E 1) (W : E m),
      Real.sinh (hdist (fermiW 1 m v W) (blk 1 m h R • fermiW 1 m v W) / 2) ^ 2 =
        (1 + ‖W‖ ^ 2) * Real.sinh (hdist v (h • v) / 2) ^ 2 + ‖R W - W‖ ^ 2 / 4 := by
  exact ⟨fermiW_measurePreserving m, fun h R v W => blk_smul_fermiW m hA1 hI1 hA hI h R v W,
    fun h R v W => disp_fermiW m hA1 hI1 hA hI h R v W⟩

end Work.Mostow
