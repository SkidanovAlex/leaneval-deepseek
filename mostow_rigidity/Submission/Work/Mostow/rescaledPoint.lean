import Mathlib
import Submission.Mostow.GapADefs

/-! Guidance from the project lead (the requester):

# GAP-A chains (lead's design; reviewed). Your request carries an exact statement; routes below.
# Vocabulary: Interfaces, HLDefs (NearIdAt, MultThickProp, ...), SubHypDefs (fermi, blk, resStd, nrmStd, nearGrp, CovolLB),
# GeodDefs (fermiW, rotN), GapADefs (GapAProp, chord). PROVED lemmas you may import: zassenhausNilpotent, frobeniusCommute,
# finite_of_nilpotent_fg_torsion, nilp_torsionGen_finite, margulisIndex, thickMax, covol_of_thick, fermi_inv,
# cosh_hdist_fermi, blk_smul_fermi, disp_blk, fermi_measurePreserving, tubeMeasure_ball2, elliptic_normal_form,
# even_normal_dim, conj_fundamentalDomain, fermiW_chart, nearId_blk, ellipsoidVol, dirichletBox, frameThinFar,
# margulisCusp, margulisLox, pairStab. IN PROGRESS (import, assume their statements): KMcovol (CovolLB k, k >= 2),
# conjCount, resStd_hom_discrete, tubeIneq, thinStrataGap, jordanTorus, rescaledPoint, geodStratum, poAction_ge1,
# hypIsometry_ge1, classify_ge2, multThick_ge2.
# EVEN n (design_strata §2, NOTES_LEAD_strata_KM.md): frameThinFar gives a nontrivial near-identity element outside Γ•K;
#   if nearGrp is infinite it is nilpotent (Zassenhaus) and FG, so if all generators had finite order it would be finite
#   (nilp_torsionGen_finite) — hence an infinite-order eta-short generator. If nearGrp is finite: elliptic_normal_form,
#   even_normal_dim (stratum dim j ≡ n mod 2, j <= n-2 even), conjCount + unfolding => tubeIneq; resStd_hom_discrete +
#   CovolLB j (j >= 2) or j = 0 => covolume >= c·eta^{-alpha}, alpha = n/2 - 1 > 0: impossible for eta small (depends on V).
# ODD n >= 5 (design_geod, NOTES_LEAD_geod.md): same, strata dims odd; dim >= 3 handled by thinStrataGap (CovolLB);
#   geodesic strata (dim 1) by geodStratum (L4 stratumOfF, L5 multiplicity-1 Margulis region, L6 tube inequality,
#   jordanTorus L7, rescaledPoint L10, dirichletBox L9, ellipsoidVol L8, nearId_blk L2, fermiW_chart L1).
# rescaledPoint torus-angle encoding: angles in AddCircle (2*pi), chord x = 2 sin(‖x‖/2) (GapADefs.chord);
#   ‖R W - W‖^2 = Σ_i ρ_i(W)^2 chord(φ_i)^2 in the jordanTorus basis.
# Never use `λ` as a variable name.
==============================================================================================================
# Strata + Kazhdan–Margulis chapter (lead's decision; vocabulary Submission/Mostow/SubHypDefs.lean — DO NOT EDIT)
Decision: route (B) — ONE rank-one Kazhdan–Margulis chapter for all k ≥ 2 (KMcovol : CovolLB k, via a thick point of
maximal injectivity: thickMax + margulisIndex + nilp_torsionGen_finite + finite-group fixed point + ray-strictness +
margulisCusp/margulisLox), NO induction on k. Stratum vocabulary from design (A): Fermi coordinates about the standard
stratum (fermi/fermiInv/tubeMeasure/blk/resStd/nrmStd), elliptic normal form, even normal dimension, tube volumes.
Consequence: GAP-A closes for all EVEN n; odd n ≥ 5 still needs the k = 1 (geodesic stratum) lemma (open, lead).
Conventions: blk/resStd/nrmStd are choice-defined; their meaning comes from blk_smul_fermi (block element acts as h on
the foot, R on the normal vector). λ is a reserved token — never use it as a variable name.
Design texts follow: (B) KM evaluation, then (A) strata design. Where they overlap, KM-* names are from (B), F*-names
from (A); lemma requests carry exact statements — follow the statement, use the texts for routes.
===============================================================================================================
## GAP-A for n ≥ 4 via a Kazhdan–Margulis chapter: evaluation of option (B)

**Bottom line.** Rank-one Kazhdan–Margulis (KM) has a short proof in our vocabulary for lattices, torsion included. It works in every dimension k ≥ 2 at once, so no induction on k is needed. It closes **StratumCovol_k for every 2 ≤ k ≤ n−2**. It does **not** cover k = 1 (GeodStratumRank≥2), where KM is false.

Consequences:
- **Even n:** every elliptic fixed stratum has even dimension, so k = 1 never arises. GAP-A then follows from G1–G3 plus the KM chapter.
- **Odd n ≥ 5:** only the k = 1 case remains. It needs a separate argument; §3 gives one that is sound in the generic case, with one degenerate case still open.
- **Recommendation: (B)**, the KM chapter, plus a bespoke k = 1 lemma.

Sources I read: `NOTES_LEAD_gapA.md` and HLDefs/Interfaces on 3.22.183.58; Gelander's PCMI notes (§3, Main Lemma 3.9: the gradient of the thinness function vanishes only where it is zero); Gelander arXiv 1510.05423. The IRS proof in 1510.05423 uses Chabauty topology, IRS Borel density and Alaoglu, which is bad for Lean. What is recommended below is Gelander's Morse argument made discrete, with his use of Selberg replaced by S2.

---
## 1. Rank-one KM with torsion: yes, short (lattices)

**Statement (strong form).** For k ≥ 2 there is ε_k > 0 such that every lattice Γ ≤ PO(k,1) has a point x with d(x, γx) ≥ ε_k for all γ ≠ 1.

This is stronger than "some conjugate meets U trivially", because it also excludes elliptics with large angles. The covolume bound (KM-J) follows immediately: the ball B(x, ε_k/2) injects, so covol ≥ vol B(ε_k/2).

**Argument.**
- **Maximum exists.** Let m(u) := inf_{γ≠1} d(u, γu). It is 2-Lipschitz, being an infimum of 2-Lipschitz functions, and Γ-invariant. m > 0 somewhere, because the fixed sets of γ ≠ 1 are null and Γ is countable. By MultThickProp with N = 1, {m ≥ s₀} ⊂ Γ·K for a compact K. So m attains its maximum s at some x₀.
- **Setup.** Suppose s < ε_k and let Σ := {γ : d(x₀, γx₀) = s}. This set is finite and nonempty. The goal is one point x' arbitrarily close to x₀ where every γ ∈ Σ moves strictly more than s. Other elements move x₀ by more than s, and m is continuous, so this gives m(x') > s, a contradiction.
- **Case split** on Γ near x₀:
  - **(inf) Some infinite-order γ has d(x₀, γx₀) < ε₂.** Pigeonhole on the powers γ^j (j ≤ N₀(η)) in the compact set {g : d(x₀, gx₀) ≤ 1} gives an infinite-order γ' := γ^{j−i} that is NearIdAt x₀ η.
    - If γ' is parabolic (ClassifyProp), margulisCusp with R = 1 shows every δ with d ≤ 1 fixes ξ. A cusp point of a discrete group has no loxodromic fixing it (KM-F), so each such δ preserves horospheres. Move x₀ away from ξ.
    - If γ' is loxodromic, margulisLox with R = 1 shows every δ with d ≤ 1 preserves the pair {a, b}. Move x₀ perpendicular to the axis A. If x₀ ∈ A, pick any normal direction; this is the **only place k ≥ 2 is used**.
  - **(fin) Every element with d(x₀, ·x₀) < ε₂ has finite order.** This case uses the Margulis index lemma (KM-B): Δ := ⟨d < ε₁⟩ ⊇ Σ contains N := ⟨Δ ∩ NearId_{x₀}(η)⟩ with [Δ : N] ≤ m.
    - N is nilpotent (Zassenhaus). Its generators move x₀ by less than η ≤ ε₂, so they have finite order.
    - A finitely generated nilpotent group generated by torsion is finite (S2 plus "torsion elements of a nilpotent group form a subgroup"). So Δ is finite and fixes some y (KM-D). Move x₀ radially away from y.
- **Strict increase.** One hyperboloid identity covers the point and axis cases. Let g preserve a Lorentz subspace W (a timelike line for the point case, a timelike plane for the axis case), let p be the foot in W, and let v be the unit normal direction. Then
  cosh d(x_t, g x_t) = cosh²t · cosh d(p, gp) − sinh²t · ⟨R_g v, v⟩, with cosh d(p, gp) ≥ 1 ≥ ⟨Rv, v⟩.
  - The right side is strictly increasing in t unless d ≡ 0, and d ≡ 0 is excluded because d(x₀, g x₀) = s > 0. This also covers axis flips.
  - Horoball case, in the upper half-space with ξ = ∞ and g(z, h) = (Az + b, h): cosh d = 1 + |Az + b − z|² / (2h²), strictly increasing as h decreases.
  - The chosen direction depends only on the invariant set, not on g, so a single x' works for all of Σ.
- **Constants,** in this order: ε₂ from margulisCusp/margulisLox (R = 1) and the power pigeonhole; η := min(η_Zassenhaus, ε₂); m := N₀(η); ε₁ := 1/m; ε_k := min(ε₁, ε₂).

**Sanity check at k = 1.** The argument fails exactly where it should: ℍ¹ is its own axis, so there is no perpendicular direction.

**Arbitrary discrete Γ.** The argument uses the maximum, so it needs finite covolume. I believe KM68 holds for all discrete subgroups, but I did not verify that, and it is not needed here: the infinite-covolume case of KM-J is trivial.

## 2. StratumCovol_k follows from KM_k, including non-faithful actions

- Let Y be the fixed stratum and C ≤ Stab_Γ(Y). The restriction map ρ : Stab_G(Y) → Isom(Y) ≅ PO(k,1) has compact kernel, the pointwise fixer O(n−k). So ρ(C) is **discrete** (ρ is proper), and ker ρ ∩ C is **finite**.
- Apply KM-J to the image ρ(C) ≤ PO(k,1), not to C. This gives vol(Y/ρ(C)) ≥ v_k := vol_{ℍ^k} B(ε_k/2), or the volume is ⊤. In the ⊤ case the tube inequality already gives a contradiction.
- The kernel only appears in the fibre count of the tube inequality G3: the tube over D_Y has volume ≈ vol(D_Y) · (normal-ball volume) / |ker|. So **G3 must be stated with D_Y a fundamental domain of ρ(C)**.
- Orientation-reversing images are fine, because PO(k,1) is the full isometry group of ℍ^k.

**Proposed encoding (avoids abstract isometry charts).**
- Standard stratum Y₀ := range (incl : E k → E n), with incl the zero-padding map. It is an hdist-isometry by definition, since tpart and the inner product are unchanged.
- Every stratum has the form c • Y₀.
- On Stab(Y₀), elements are block-diagonal O(k,1) × O(n−k), and ρ is just the (k,1)-block.

## 3. k = 1 (GeodStratumRank≥2): not covered; separate argument

**KM(1) is false.** Lattices ℓℤ ≤ Isom(ℝ) have covolume ℓ → 0.

**Setting** (lead's notation):
- Y = Fix b is a geodesic, and C = C_Γ(b) acts on Y with minimal translation ℓ₀ and generator g₀.
- Q = C ∩ (pointwise fixer of Y). Each c ∈ C acts as (t_c, R_c) ∈ ℝ × Z(R_b).
- Tube inequality: ℓ₀ / |Q| ≲ V (θ_max(b)/η₁)^{n−1}.
- z is at distance r_z from Y, with e^{r_z} ≲ η / θ_min(b).
- The displacement of c at z is ≲ (|t_c| + ‖R_c − 1‖) e^{r_z}.

**Proposed "Blichfeldt screw" lemma.**
1. **Reduce to an abelian torus.** Q_A := near-identity part of Q (abelian, index ≤ J). R₀ normalises the torus spanned by Q_A, so R₀^w centralises it for some w ≤ |Weyl| ≤ n!. Then C' := ⟨g₀^w⟩·Q_A is abelian, with rotations in a torus T of rank ≤ r = (n−1)/2. The cost is a bounded factor wJ in covolume. This handles equal-angle blocks.
2. **Apply Blichfeldt** (Mathlib's pair lemma for fundamental domains) in ℝ × T to B = (−δ₁, δ₁) × U_{δ₂}. The covolume is wℓ₀ / |Q_A|, and the Haar share of U_{δ₂} is ≳ δ₂^r independently of Q. Blichfeldt gives c ≠ 1 in C' ∩ B⁻¹B.
3. **c has infinite order.** Take δ₂ < θ_b/3. Since b has minimal angle in A_P, nontrivial elements of Q_A have some angle ≥ θ_b, so c ∉ Q_A. Hence t_c ≠ 0 and c is loxodromic.
4. **c is ε-short at z.** Take δ₁, δ₂ ≈ ε e^{−r_z}.
5. **Condition:** δ₁ δ₂^r ≳ ℓ₀ / |Q|. Using the tube bound, with θ_min ≈ θ_max = θ, this reads θ^{r+1} ≳ V θ^{2r} (up to η, ε constants). It holds for every r ≥ 1 once η ≪ ε (η may depend on V, as in n = 3). For r = 1 this recovers the lead's n = 3 bound.

**Still open:** the case θ_min(b) ≪ θ_max(b)^{2r/(r+1)}, where z lies along a small-angle block. A possible fix is to replace the round tube by the C'-invariant thickened torus orbit {(s, ρ, t·w) : t ∈ T, ρ ≈ r_z}. That set lies in T_b because R_b commutes with T. I have not checked it.

## 4. Recommendation and lemmas

**Recommendation: (B).** One dimension-generic KM chapter of about 11 lemmas, plus about 4 transport lemmas, all rated certain. It replaces the lead's unverified even-k induction sketch and closes all k ≥ 2 strata. Keep a bespoke (A)-style lemma for k = 1 only.

Before dispatch, check two things:
- margulisCusp, margulisLox, Zassenhaus and MultThick must be proved for general n, including n = 2, and not only for n ≥ 3.
- ClassifyProp must also be available for general n.

Helper definitions:
```
thick Γ u := ⨅ γ : {γ : Γ // γ ≠ 1}, hdist u ((γ:PO n 1) • u)
incl (h : k ≤ n) : E k → E n        -- zero padding;  Y0 h := Set.range (incl h)
```

**Lemmas, all certain now:**

**KM-A cellCover** (shared with S1).
`∀ η>0, ∃ m:ℕ, ∀ x, ∃ cell : PO n 1 → Fin m, ∀ g h, hdist x (g•x) ≤ 1 → hdist x (h•x) ≤ 1 → cell g = cell h → NearIdAt (g⁻¹*h) x η`
Sketch: conjugate x to 0 with a boost; {g : d(0, g0) ≤ 1} is compact; cover it by finitely many left translates of a set V with V⁻¹V ⊂ NearId(η).

**KM-B margulisIndex.**
`∀ η>0, ∃ ε>0, ∃ m, ∀ Γ, IsDiscrete ↑Γ → ∀ x, let Δ := Subgroup.closure {g | g ∈ Γ ∧ hdist x (g•x) < ε}; (Subgroup.closure {g | g ∈ Δ ∧ NearIdAt g x η}).relindex Δ ≤ m`
Sketch: ε := 1/m. If there are more than m cosets, follow a path of length m through distinct cosets in the Schreier graph. All its prefixes move x by at most 1, so two share a cell, and their quotient lies in N. Contradiction.

**KM-C nilpTorsionGenFinite.**
`Group.IsNilpotent H → Group.FG H → Subgroup.closure {h : H | IsOfFinOrder h} = ⊤ → Finite H`
Sketch: in a nilpotent group the torsion elements form a subgroup (induct on the upper central series); then apply S2.

**KM-D finiteFixes.**
`(F : Subgroup (PO n 1)) → Finite F → ∃ y, ∀ g ∈ F, g • y = y`
Sketch: Σ_{g∈F} (lift of g·hlift u) is future timelike and F-invariant; normalise it onto the hyperboloid.

**KM-E rayStrict.** Three statements, each with the new point x' independent of g:
- (i) Point case: `g•y=y → 0<hdist x (g•x) → hdist x (g•x) < hdist x' (g•x')`, where x' is on the ray from y through x, beyond x.
- (ii) Axis case: `2≤n → ∀ τ>0, ∃ x', hdist x x' < τ ∧ ∀ g, g preserves {a,b} → 0<hdist x (g•x) → hdist x (g•x) < hdist x' (g•x')`
- (iii) Horoball case: the same, for all g with `bd g ξ = ξ ∧ busemann ξ (g•0)=0`.

Sketch: the hyperboloid identity in §1 for (i) and (ii); the upper-half-space formula for (iii).

**KM-F cuspNoLox.**
`IsDiscrete ↑Γ → IsParabolic q → q∈Γ → bd q ξ = ξ → g∈Γ → bd g ξ = ξ → busemann ξ (g•0) = 0`
Sketch: if g were loxodromic at ξ, the conjugates g^{-j} q g^{j} would tend to 1, contradicting discreteness.

**KM-G shortInfinite.**
`∃ ε₂>0, ∀ Γ discrete, ∀ x (γ:Γ), ¬IsOfFinOrder γ → hdist x (γ•x) < ε₂ → (∃ ξ ∈ Sph n, ∀ δ:Γ, hdist x (δ•x) ≤ 1 → bd δ ξ = ξ ∧ busemann ξ (δ•0) = 0) ∨ (∃ a b, a∈Sph n ∧ b∈Sph n ∧ a≠b ∧ ∀ δ:Γ, hdist x (δ•x) ≤ 1 → (bd δ a = a ∧ bd δ b = b) ∨ (bd δ a = b ∧ bd δ b = a))`
Sketch: KM-A applied to powers of γ; then ClassifyProp, margulisCusp or margulisLox with R = 1, and KM-F.

**KM-H thickMax.**
`HypLattice Γ → ∃ x₀, 0 < thick Γ x₀ ∧ ∀ u, thick Γ u ≤ thick Γ x₀`
Sketch: thick is 2-Lipschitz; MultThickProp with N = 1; fixed sets of γ ≠ 1 are volH-null.

**KM-I KMthick.**
`2 ≤ k → ∃ ε>0, ∀ Γ : Subgroup (PO k 1), HypLattice Γ → ∃ x, ∀ γ:Γ, γ≠1 → ε ≤ hdist x ((γ:PO k 1)•x)`
Sketch: §1. At the maximiser, KM-G or KM-B/C/D supplies an invariant set, and KM-E produces x' with m(x') > m(x₀).

**KM-J KMcovol.**
`2 ≤ k → ∃ v>0, ∀ (Γ : Subgroup (PO k 1)) D, IsDiscrete ↑Γ → IsFundamentalDomain Γ D (volH k) → ENNReal.ofReal v ≤ volH k D`
Sketch: if the volume is ⊤ there is nothing to prove; otherwise use KM-I and unfolding of the injected ball B(x, ε/2).

**Transport lemmas (certain; T4 is the heavy one):**
- **T1 inclIsom:** `hdist (incl h v) (incl h v') = hdist v v'`. Immediate.
- **T2 resY0:** a homomorphism `{g : PO n 1 // g • Y0 h = Y0 h} →* PO k 1` with `incl h (resY0 g • v) = g • incl h v`. It is the (k,1)-block.
- **T3 resDiscrete:** a discrete subgroup of the stabiliser has discrete image under resY0 and finite kernel. Sketch: properness, since the kernel is O(n−k).
- **T4 fixStratum:** `g ≠ 1 → (∃ p, g•p = p) → ∃ k (h : k ≤ n) (c : PO n 1), {u | g•u = u} = c • Y0 h`. Sketch: the 1-eigenspace of a Lorentz matrix containing a timelike vector has signature (k,1); then Lorentz Gram–Schmidt / Witt. This needs the most linear algebra.
- **T5 StratumCovol_k:** for 2 ≤ k, if C ≤ Γ stabilises c•Y0 and D_Y is a fundamental domain of `((c⁻¹Cc).map resY0)` in E k, then v_k ≤ volH k D_Y. Sketch: KM-J plus T3. G3 must be restated with this D_Y.

**Not yet certain:**
- **k = 1 GeodBlichfeldt** (odd n ≥ 5): the §3 steps 1–5 are sound in the generic case (θ_min ≈ θ_max, including equal-angle blocks via the Weyl power). The unequal-magnitude case is open; the candidate fix is the thickened torus-orbit region.
- **Suggested next step:** a separate design pass on that k = 1 case, before any n ≥ 5 odd dispatch.
===============================================================================================================
I read the n = 3 design, `Interfaces.lean`, `HLDefs.lean` and the `ChallengeDeps` definitions of `PO`, `MatrixSum` and the `pmOneMat` star. Short version: GAP-A closes for every even n ≥ 4, but for odd n ≥ 5 it still needs one open lemma, GeodStratum(N) for odd N ≥ 5.

# GAP-A for n ≥ 4: sub-hyperbolic vocabulary, StratumCovol and GeodStratum

## 0. Verdict

- **Induction on n.** GAP-A in dimension k < n is the wrong hypothesis to induct on. GAP-A is non-uniform in Γ: its compact K depends on the lattice. The strata of Γ come with infinitely many different stabiliser lattices C̄, and the argument needs a bound that holds for all of them at once. The right hypothesis is the uniform statement **COV(k)**: every discrete Λ ≤ PO(k,1) has covolume ≥ v_k > 0. This is Kazhdan–Margulis–Wang for PO(k,1).
- **COV(k) is proved by the same machinery in dimension k.** The inputs are G1–G3 from NOTES_LEAD_gapA, the tube inequality, and COV(j) for smaller j.
- **Parity fixes the stratum dimension.** A near-identity elliptic element is orientation preserving, so its normal rotation has det 1 and no fixed vector, and the normal dimension m is even (lemma F13). So strata have dim j ≡ n (mod 2).
  - For **even n**, strata have dimension 0, 2, …, n−2, and geodesic strata (j = 1) never occur.
  - For **odd n**, strata have dimension 1, 3, …, n−2.

| Result | Status |
|---|---|
| COV(2) | closes (point strata only) |
| COV(even k) | closes by induction on even j < k |
| COV(3) | closes (rank-1 geodesic case = the n = 3 chain) |
| GAP-A(n), n even ≥ 4 | closes: needs COV(2), COV(4), …, COV(n−2) |
| GAP-A(4) | closes: needs COV(2) only |
| GAP-A(n), n odd ≥ 5 | needs COV(3, 5, …, n−2) and GeodStratum(n) |
| COV(odd k ≥ 5) | needs GeodStratum(k) |
| GeodStratum(N), odd N ≥ 5 | the only remaining gap; not closed |

- **Non-faithful and non-uniform C̄ are harmless.** COV is a statement about any discrete image group in PO(j,1) of finite covolume. The kernel is finite and enters only as the factor Nat.card K in the tube formula.

## 1. Chapter SubHyp: the sub-hyperbolic-space vocabulary

**Convention: never state anything for a general subspace W.** Conjugate Γ so that the stratum is the standard one, then work in `PO (k+m) 1`. n is always a bound variable in these statements, so `obtain ⟨k, m, rfl⟩` works at the use site. The general-W form `TG W := {u | hlift u ∈ W}` appears only in F12, as the bridge from `fixSet`.

### Definitions

The k-dependence is carried by the pair (k, m) with n = k + m.

```
def coordEmb (k m) (v : E k) : E (k+m) := WithLp.toLp 2 (Fin.append (fun i => v i) 0)
def tanC  (k m) (u : E (k+m)) : E k := WithLp.toLp 2 (fun i => u (Fin.castAdd m i))
def nrmC  (k m) (u : E (k+m)) : E m := WithLp.toLp 2 (fun i => u (Fin.natAdd k i))
def stdTG (k m) : Set (E (k+m)) := Set.range (coordEmb k m)            -- = {u | nrmC u = 0}
def sinhc (s : ℝ) : ℝ := if s = 0 then 1 else Real.sinh s / s
/ -- Fermi coordinates about stdTG: foot v, normal vector w with ‖w‖ = distance - /
def fermi (k m) (v : E k) (w : E m) : E (k+m) :=
  WithLp.toLp 2 (Fin.append (fun i => Real.cosh ‖w‖ * v i) (fun i => sinhc ‖w‖ * w i))
def tube (k m) (ρ : ℝ) : Set (E (k+m)) := {u | ‖nrmC k m u‖ ≤ Real.sinh ρ}
def tubeMeasure (k m) : Measure (E m) :=
  volume.withDensity (fun w => ENNReal.ofReal (Real.cosh ‖w‖ ^ k * sinhc ‖w‖ ^ (m-1)))
def fixSet (g : PO n 1) : Set (E n) := {u | g • u = u}
def TG (W : Submodule ℝ (Fin n ⊕ Fin 1 → ℝ)) : Set (E n) := {u | hlift u ∈ W}
def linFix (A : O1 n) := LinearMap.ker (Matrix.toLin' (tsign A • mat A) - LinearMap.id)
def SetStabStd (k m) : Subgroup (PO (k+m) 1) := {g | ∀ u, u ∈ stdTG k m ↔ g • u ∈ stdTG k m}
def nearGrp (Λ : Subgroup (PO n 1)) (z : E n) (η : ℝ) : Subgroup (PO n 1) :=
  Subgroup.closure {g | g ∈ Λ ∧ NearIdAt g z η}
```

**Block elements, defined without block matrices.** F4 shows that the map below is an isometry of E (k+m). HypIsometryProp clause 8 then gives an element of PO, chosen with `Classical.choose`.

```
def blkMap (k m) (h : PO k 1) (R : E m ≃ₗᵢ[ℝ] E m) (u : E (k+m)) : E (k+m) :=
  let p := (fermiEquiv k m).symm u; fermi k m (h • p.1) (R p.2)
def blk (k m) (h) (R) : PO (k+m) 1 := Classical.choose (HypIsometry.clause8 (blkMap_isometry k m h R))
```

`fermiEquiv` is F1. The restriction hom `res : SetStabStd k m →* PO k 1` and the normal-part hom `nrm : SetStabStd k m →* (E m ≃ₗᵢ[ℝ] E m)` both come from the unique decomposition in F6.

### Lemmas

Tags: [NOW] = certain and dispatchable immediately; [NOW|X] = certain, depends on X.

- **F1 `fermiEquiv`** [NOW]: `fermi k m` is a homeomorphism `E k × E m ≃ₜ E (k+m)`.
  - Inverse: s = arsinh ‖nrmC u‖, w = s·nrmC u/‖nrmC u‖ (0 if nrmC u = 0), v = tanC u / cosh s.
  - Also `tpart (fermi v w) = cosh ‖w‖ * tpart v`, which is algebra with cosh² − sinh² = 1.

- **F2 `cosh_hdist_fermi`** [NOW]:
  `cosh (hdist (fermi v w) (fermi v' w')) = cosh‖w‖ * cosh‖w'‖ * cosh (hdist v v') − sinhc‖w‖ * sinhc‖w'‖ * ⟪w, w'⟫`.
  - Sketch: unfold hdist; tpart comes from F1 and the inner product splits over `Fin.append`.

- **F3 `dist_stdTG`** [NOW|F2]:
  `hdist (fermi v w) (coordEmb k m v) = ‖w‖ ∧ ∀ v', ‖w‖ ≤ hdist (fermi v w) (coordEmb k m v')`.
  Corollary: `u ∈ tube k m ρ ↔ ∃ v', hdist u (coordEmb v') ≤ ρ`.
  - Sketch: F2 with w' = 0 gives cosh D = cosh‖w‖·cosh d(v,v') ≥ cosh‖w‖.

- **F4 `blkMap_isometry`, `blk_smul_fermi`** [NOW|F2, T2]:
  `blk k m h R • fermi k m v w = fermi k m (h • v) (R w)`.
  - Sketch: the right-hand side of F2 is invariant under (h, R); then clause 8.

- **F5 `blk_mul`, `blk_one`, `blk_injective`** [NOW|F4, faithfulness clause 6]:
  `(h, R) ↦ blk h R` is an injective monoid hom from `PO k 1 × (E m ≃ₗᵢ E m)`.
  - Sketch: compare the actions on fermi points, then use faithfulness.

- **F6 `stab_eq_blk`** [NOW, moderate]:
  `g ∈ SetStabStd k m → ∃! p : PO k 1 × (E m ≃ₗᵢ[ℝ] E m), g = blk k m p.1 p.2`.
  - h comes from clause 8 applied to `v ↦ tanC (g • coordEmb v)`, which is an isometry of E k by F3.
  - Then g' := blk h⁻¹ 1 * g fixes stdTG pointwise. Its tsign-normalised matrix fixes span(e_{inl i<k}, e_{inr}) = W. Unitarity for pmOneMat makes it preserve W^⊥, and the W^⊥ block is an orthogonal R.
  - Define `res`, `nrm` from this; the hom property follows from uniqueness and F5.

- **F7 `disp_blk`** [NOW|F2]. For u = fermi v w, s = ‖w‖ and ŵ = w/s:
  `sinh (hdist u (blk h R • u) / 2) ^ 2 = cosh s ^ 2 * sinh (hdist v (h•v) / 2) ^ 2 + sinh s ^ 2 * ‖R ŵ − ŵ‖ ^ 2 / 4`.
  - Sketch: F2 with v' = h v, w' = Rw; use 1 − ⟪ŵ, Rŵ⟫ = ‖Rŵ − ŵ‖²/2 and cosh x − 1 = 2 sinh²(x/2).
  - This formula replaces all screw-displacement estimates, including S5 and S10 of the n = 3 chain.

- **F8 `fermi_measurePreserving`** [NOW, the heaviest item]:
  `MeasurePreserving (fun p => fermi k m p.1 p.2) ((volH k).prod (tubeMeasure k m)) (volH (k+m))`.
  - Sketch: Jacobian of fermi. The volume element is cosh^k s · sinh^{m−1} s ds dσ dvol_k.
  - Use `lintegral_image_eq_lintegral_abs_det_fderiv_mul` with the explicit inverse from F1. For m = 0 it is trivial.

- **F9 `tubeMeasure_ball`** [NOW]: the tube volume c(n,k,ρ), with n = k + m and 1 ≤ m.
  `tubeMeasure k m (closedBall 0 ρ) = σ_{m−1} ∫₀^ρ cosh^k s sinh^{m−1} s ds`, and for ρ ≥ 1:
  `c₁(n) e^{(n−1)ρ} ≤ tubeMeasure k m (closedBall 0 ρ) ≤ c₂(n) e^{(n−1)ρ}`.
  - Sketch: polar coordinates, via `integral_fun_norm_addHaar` or the lintegral version.

- **F10 `tube_quot_volume`** [NOW|F4, F5, F6, F8, F11]: the induced covolume. Hypotheses:
  - `Λ ≤ SetStabStd k m`, `IsDiscrete Λ`, `K := Λ ⊓ res.ker` (finite by F11);
  - `IsFundamentalDomain (Λ.map res) DY (volH k)`;
  - `B ⊆ E m` measurable with `∀ λ ∈ Λ, nrm λ '' B = B`;
  - `IsFundamentalDomain Λ D (volH (k+m))`.

  Conclusion: `volH (k+m) (D ∩ fermi '' (univ ×ˢ B)) * Nat.card K = volH k DY * tubeMeasure k m B`.
  - Sketch: fermi''(DY' ×ˢ FK) is a fundamental domain for Λ on the invariant set. DY' removes the null set of points with nontrivial res-stabiliser. FK is a fundamental domain of nrm K on E m, which acts a.e. freely because K ∩ ker nrm = 1 by F5 and nontrivial fixed subspaces are null.
  - Finish with `IsFundamentalDomain.measure_set_eq`. For k = 0, E 0 is a point and `volH 0 univ = 1`, since tpart 0 = 1 and the Lebesgue measure on ℝ⁰ is a Dirac mass.

- **F11 `res_discrete`** [NOW]: `IsDiscrete Λ → Λ ≤ SetStabStd k m → IsDiscrete (Λ.map res) ∧ Finite ↥(Λ ⊓ res.ker)`.
  - Sketch: blk '' (compact × O(m)) is compact because O(m) is compact; intersect with a discrete set.

- **F12 `elliptic_normal_form`** [NOW, matrix algebra]:
  `g • p = p → ∃ k m (e : k+m = n) (h : PO n 1) (R : E m ≃ₗᵢ E m), (∀ w, R w = w → w = 0) ∧ h⁻¹*g*h = e ▸ blk k m 1 R`.
  - Also `fixSet g = TG (linFix (rep g))`.
  - Sketch: take a Minkowski-orthonormal basis of linFix starting from hlift p (Gram–Schmidt; its orthogonal complement in W is positive definite). Extend it and form the O1 element. Use a boost if tsign = −1.

- **F13 `even_normal_dim`** [NOW]: `NearIdAt (blk k m 1 R) z η → η ≤ η₀ → (∀ w, R w = w → w = 0) → Even m`.
  - Sketch: near-identity at z gives det R = 1. Conjugate z to 0; the tsign-normalised matrix is near 1, and it equals diag(1, R).
  - For odd m, det(R − 1) = det(1 − Rᵀ) = (−1)^m det(R − 1), so det(R − 1) = 0 and R has a fixed vector.

- **F14 `conj_lattice`** [NOW|T2]: `IsFundamentalDomain Γ D → IsFundamentalDomain (Γ.map (MulAut.conj h)) (h • D)` with the same volH.

## 2. The DAG for n ≥ 4

Two statements are formulated here, and GeodStratum(N) comes in §3.

```
def CovolLB (k : ℕ) : Prop := ∃ v : ℝ, 0 < v ∧ ∀ Λ : Subgroup (PO k 1), IsDiscrete (SetLike.coe Λ) →
  ∀ D, IsFundamentalDomain Λ D (volH k) → ENNReal.ofReal v ≤ volH k D
def FinTypeTube (N : ℕ) : Prop :=          -- the one engine used by both COV(N) and GAP-A(N)
  ∃ η₀ c α : ℝ, 0 < η₀ ∧ 0 < c ∧ 0 ≤ α ∧ (3 ≤ N → 0 < α) ∧ ∀ η ∈ Set.Ioc 0 η₀,
  ∀ Λ D, IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH N) → ∀ z,
    nearGrp Λ z η ≠ ⊥ → Finite (nearGrp Λ z η) →
    ENNReal.ofReal (c * η ^ (-α)) ≤ volH N D
```

`FinTypeTube N` holds for even N ≥ 2, where (c, α) are allowed to use COV of smaller even dimensions. For odd N it is replaced by §3.

### Lemmas

- **G1 Jordan–Frobenius, G2 ConjCount (general n), S7 unfold** — as in NOTES_LEAD_gapA. They are certain there. G2's torus count is by the Weyl group, 2^{⌊n/2⌋}⌊n/2⌋!.

- **G3' `tubeIneq`** [certain|G1, G2, S7, F7, F10]. Setting: Λ has already been conjugated by F12 and F14.
  - Hypotheses: `b = blk j m 1 R ∈ Λ`, R has no fixed vector, `θ := ‖R − 1‖`, `C := centralizer {b} ⊓ Λ` (so `C ≤ SetStabStd`, since C preserves Fix b), `K := C ⊓ res.ker`, `DY` a fundamental domain of `C.map res`, and `2*sinh(ρ+1)*θ ≤ η₁`.
  - Conclusion: `volH j DY * tubeMeasure j m (closedBall 0 ρ) ≤ C(n) * Nat.card K * volH n D`.
  - Sketch: by F7 the fermi tube lies in T_b. Unfold over Γ using G2's cosets of C, then apply F10 to C.

- **G4 `card_K`** [certain|G1]: `(∀ κ ∈ K, κ ≠ 1 → ‖nrm κ − 1‖ ≤ θ_J → θ ≤ ‖nrm κ − 1‖) → Nat.card K ≤ J(n) * (C₀/θ)^(m/2)`.
  - Sketch: the near-identity part has index ≤ J and is abelian, so it lies in one maximal torus of dimension m/2. Its elements are θ-separated, so pack them.
  - Choose b as the ‖nrm − 1‖-minimal element of A_P, as in the lead's notes. Then θ_b ≤ Cη whenever nearGrp Λ z η ≠ ⊥.

- **K1 `covol_of_thick`** [NOW|T2]: `(∀ λ ∈ Λ, NearIdAt λ p η → λ = 1) → ofReal (c(k,η)) ≤ volH k D`.
  - Sketch: #{λ | d(p,λp) < 2r} ≤ N(k,η) by pigeonhole in the compact set of displacement ≤ 2r. Two elements in one cell would give a nontrivial NearIdAt quotient. So vol B(p,r)/N ≤ covol.

- **K2 `elem_of_allInfinite`** [certain, medium|Zassenhaus, S2, ClassifyProp]:
  `η ≤ η_Z → (∀ p, Infinite (nearGrp Λ p η)) → ∃ ξ ∈ Sph k, (∀ λ ∈ Λ, bd λ ξ = ξ) ∨ ∃ ξ', ξ' ≠ ξ ∧ ∀ λ ∈ Λ, pair-preserving`.
  - Sketch: nearGrp is infinite and nilpotent, so it has a canonical boundary fixed set Φ(p): one point or one pair. For d(p,p') small, both groups lie in nilpotent nearGrp p (2η), so Φ is locally constant.
  - ℍ is connected, so Φ is constant. Since Φ(λp) = λΦ(p), all of Λ fixes Φ.

- **K3 `not_lattice_of_elem`** [certain, medium|F10, margulisCusp-type]: `2 ≤ k →` a Λ as in K2's conclusion has no finite-volume fundamental domain.
  - Parabolic case: horoball fibres give infinite volume.
  - Pair case: F10 with j = 1 and ρ → ∞ gives volume ℓ·e^{(k−1)ρ}/|K| → ∞.

- **T-even `finTypeTube_even`** [certain|G3', G4, F9, F13, CovolLB j for even 2 ≤ j < N]. This gives FinTypeTube N for even N.
  - At z, pick b as in G4. By F13, j = N − m is even.
  - G3' with e^ρ ≍ η₁/θ gives covol ≥ c·vol(Y/C̄)·θ^{m/2−(N−1)}. Here vol(Y/C̄) is 1 if j = 0 and ≥ v_j if j ≥ 2.
  - The exponent satisfies (N−1) − m/2 ≥ N/2 − 1, and θ ≤ Cη, so α = N/2 − 1.

- **COV-step `covolLB_of_finTypeTube`** [certain|K1, K2, K3]: `FinTypeTube k → 2 ≤ k → CovolLB k`.
  - Either some point is thick (K1), or some point is of finite nontrivial type (FinTypeTube), or every point is of infinite type, which K2 and K3 rule out.
  - COV(2) is the base case: all strata are points (j = 0), so no induction hypothesis is used.

- **GAPA-even `gapA_even`** [certain|S1 FrameThinFar, FinTypeTube n]: for even n ≥ 4 and HypLattice Γ with V = volH D.
  - Choose η with c·η^{−α} > V (possible since α > 0), and take K from S1(min(η, ε)).
  - Outside Γ•K, nearGrp ≠ ⊥ and it cannot be finite, so it is infinite. It is nilpotent (Zassenhaus). If every generator had finite order it would be torsion and finitely generated, hence finite by S2. So some generator has infinite order and is η-short, with η ≤ ε.

- **COV(3)** [certain|n = 3 chain S3–S10 rewritten in F7]: the same trichotomy with a scale window.
  - Use a point with nearGrp(η) ≠ ⊥ and every element of Λ with d(z,λz) ≤ Aη of finite order. Such a point exists: otherwise, by the lox-power lemma L6 (NOTES_LEAD_K0), every point is of infinite type at scale A'η, and K2 and K3 apply.
  - S3–S10 give either the screw with d ≤ C(1 + V/η₁²)η, which contradicts the window when V ≤ 1, or a contradiction outright. So V ≥ 1 or V ≥ c.

### Assembly

- n = 4, 6, 8, …: COV(2) → T-even(4) → COV(4) → … → GAPA-even(n). All nodes are certain given G1–G3', and the only heavy analytic item is F8.
- n = 5: GAP-A(5) = S1 + COV(3) + GeodStratum(5).
- n = 7: additionally needs COV(5), which needs GeodStratum(5), plus GeodStratum(7).

## 3. GeodStratum(N) for odd N ≥ 5: statement, what is certain, and where it fails

This is the one statement that is not closed. It has two uses: in GAP-A(N) it produces the short element; in COV(N) it produces a contradiction with the scale window.

```
def GeodStratumProp (m : ℕ) : Prop :=  -- ambient N = 1 + m, m even
  ∃ C η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Set.Ioc 0 η₀, ∀ Λ D, IsDiscrete (SetLike.coe Λ) →
  IsFundamentalDomain Λ D (volH (1+m)) → volH _ D ≠ ⊤ → ∀ (z : E (1+m)) (R : E m ≃ₗᵢ[ℝ] E m),
  blk 1 m 1 R ∈ Λ → (∀ w, R w = w → w = 0) → NearIdAt (blk 1 m 1 R) z η → [G4-minimality of R] →
  ∃ γ ∈ Λ, ¬ IsOfFinOrder γ ∧ hdist z (γ • z) ≤ C * (1 + (volH _ D).toReal) * η
```

- **m = 2 (N = 3)** is exactly S3–S10 and is certain.
- **The displacement form suffices for COV.** If V ≤ 1, the element has displacement ≤ 2Cη, which contradicts the window with A = 2C.

### Certain tools for it

- **PS `ballImage_le`** [NOW, general unfolding]:
  `IsFundamentalDomain C DC → (∀ c ∈ C, (c • ball z r ∩ ball z r).Nonempty → c ∈ S) → volH (ball z r) ≤ Nat.card S * volH (DC ∩ C • ball z r)`.

- **Screw packing**, from PS + F10 with j = 1. Suppose no infinite-order element of C⁺ (the translation part, index ≤ 2) has d(z,γz) < 2r, where d = d(z,Y) and K_z := {κ ∈ K | d(z,κz) < 2r}. Then
  `vol B_r · |K| ≤ #K_z · ℓ · tubeMeasure(annulus d ± r)`, i.e. `|K|/#K_z ≲ ℓ e^{(N−1)d}/r^N`.
  - Combined with G3' (ℓ ≤ C V |K| / tubeMeasure(B_ρ)), the screw exists as soon as
    **(★) e^{(N−1)(ρ−d)} ≫ V · #K_z(2r) / r^N**, with r ≍ (1+V)η.
  - (★) replaces the lead's torus pigeonhole in O(N−1)/K. It makes no assumption on R_g centralising A_P, and equal-angle blocks do not matter to it.

### The generic case closes

Suppose all rotation angles of R are within a factor κ of θ. Then F7 gives sinh d ≤ η/θ and sinh ρ ≍ η₁/(κθ), so ρ − d ≥ log(η₁/(κη)). The count #K_z(2r) is O_κ(1) when ŵ has a component in every eigenplane of the torus. With these, (★) holds.

### Where it fails (the real gap)

The problem is **z near a larger stratum Y' ⊋ Y**. Take ŵ in one slow plane P₂ of R with angle θ₂ ≪ θ₁.
- Then #K_z ~ |K|/|K·ŵ| can be ~ θ^{−(m/2−1)}: every element rotating only the other planes is short at z.
- The round tube radius ρ, fixed by the operator norm θ₁, can be smaller than d, which is fixed by θ₂.
- Both sides of (★) then degrade, and the isotropic G3' is too weak.

In the true geometry this z sits in the Margulis region of a stratum of dimension 1 + 2(m/2 − 1) = N − 2. So the correct Y is Fix(H) for the local group H = nearGrp at a window scale, not Fix b for a single element.

**What I think fixes it (not verified):**
- **G2-grp, ConjCount for finite subgroups:** γHγ⁻¹ and H near-identity at the same w generate a finite, nilpotent, near-identity group. By Frobenius it is abelian and lies in one torus. So it contributes ≤ |W(n)| cosets of N_Γ(H).
- Use it with Y := Fix nearGrp(z, s), where s is chosen by a pigeonhole over ≤ n scale windows so that Fix is stable across [s, As]. Then K_z ⊆ PtStab(Y) at scale s.
- dim Y ≥ 2 is handled by COV (§2). dim Y = 1 then has every short element of K fixing Y and no slow plane, which is the generic case above.

The pieces to check are G2-grp and the window pigeonhole, lemma W: stable Fix over a factor-A scale window within n + 1 steps. I would send this to a crux pass rather than dispatch it now.

## 4. Not needed

- GAP-A in lower dimensions (non-uniform, useless as an induction hypothesis).
- Selberg's lemma, finite generation, Garland–Raghunathan.
- Citing Kazhdan–Margulis for even n, since COV(even) is proved.
- Block-matrix definitions: blk comes from clause 8 and the matrix algebra is confined to F6 and F12.
- General-W versions of F2–F10 (conjugate instead, F12 + F14).
- Riemannian exponential maps and normal bundles (fermi is an explicit formula).
- Chabauty or IRS arguments; bounded torsion K0; finiteness of cusp classes.
- The lead's rank-≥2 torus pigeonhole and its degenerate subcases, which (★) replaces.

## Dispatch now

- **Pure vocabulary:** F1–F7, F9, F11–F14, PS.
- **Heavy but certain:** F8 and then F10.
- **Group theory:** K1, K2, K3, G4.
- **Once G1–G2 exist:** G3', T-even, the COV step, gapA_even and COV(3).

Hold GeodStratum(N ≥ 5) and G2-grp for a separate crux pass. Whether Mostow may cite it for odd n ≥ 5 is the open decision.
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

/-- The chord `2 sin(‖x‖/2)` of an angle of the circle of circumference `2π` is nonnegative. -/
lemma rescaledPoint_chord_nonneg (x : AddCircle (2 * Real.pi)) : 0 ≤ chord x := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnorm : ‖x‖ ≤ Real.pi := by
    have := AddCircle.norm_le_half_period (p := 2 * Real.pi) (x := x) (by positivity)
    rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at this
    linarith
  have hs : 0 ≤ Real.sin (‖x‖ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith)
  unfold chord
  nlinarith

/-- The chord vanishes only at the origin of the circle. -/
lemma rescaledPoint_chord_eq_zero (x : AddCircle (2 * Real.pi)) : chord x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : Real.sin (‖x‖ / 2) = 0 := by
      have h2 : (2 : ℝ) * Real.sin (‖x‖ / 2) = 0 := by simpa [chord] using h
      exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hnorm : ‖x‖ ≤ Real.pi := by
      have := AddCircle.norm_le_half_period (p := 2 * Real.pi) (x := x) (by positivity)
      rw [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at this
      linarith
    have h1 : -Real.pi < ‖x‖ / 2 := by have := norm_nonneg x; linarith
    have h2 : ‖x‖ / 2 < Real.pi := by linarith
    have h3 : ‖x‖ / 2 = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt h1 h2).mp hs
    have h4 : ‖x‖ = 0 := by linarith
    exact norm_eq_zero.mp h4
  · intro h
    simp [h, chord]

theorem rescaledPoint (r : ℕ) (A : AddSubgroup (Fin r → AddCircle (2 * Real.pi))) [Finite A]
    (ρ : Fin r → ℝ) (hρ : ∀ i, 0 < ρ i) (δ : ℝ) (hδ : 0 < δ)
    (f : Fin r → AddCircle (2 * Real.pi)) (hfA : f ∈ A) (hf0 : f ≠ 0)
    (hf : ∑ i, ρ i ^ 2 * chord (f i) ^ 2 ≤ δ ^ 2) :
    ∃ s : ℝ, 1 ≤ s ∧ ∃ b ∈ A, b ≠ 0 ∧ ∑ i, (s * ρ i) ^ 2 * chord (b i) ^ 2 = δ ^ 2 ∧
      ∀ a ∈ A, a ≠ 0 → δ ^ 2 ≤ ∑ i, (s * ρ i) ^ 2 * chord (a i) ^ 2 := by
  classical
  -- `A` is finite, so we can minimise the weighted square-length over `A \ {0}`.
  haveI : Fintype A := Fintype.ofFinite A
  have hpos : ∀ a : A, (a : Fin r → AddCircle (2 * Real.pi)) ≠ 0 →
      0 < ∑ i, ρ i ^ 2 * chord ((a : Fin r → AddCircle (2 * Real.pi)) i) ^ 2 := by
    intro a ha
    have hex : ∃ i, (a : Fin r → AddCircle (2 * Real.pi)) i ≠ 0 := by
      by_contra h
      have hall : ∀ i, (a : Fin r → AddCircle (2 * Real.pi)) i = 0 := by
        intro i
        by_contra hne
        exact h ⟨i, hne⟩
      exact ha (funext hall)
    obtain ⟨i, hi⟩ := hex
    refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
    · have := rescaledPoint_chord_nonneg ((a : Fin r → AddCircle (2 * Real.pi)) j); positivity
    · have hc : chord ((a : Fin r → AddCircle (2 * Real.pi)) i) ≠ 0 :=
        fun h0 => hi ((rescaledPoint_chord_eq_zero _).mp h0)
      have h1 : 0 < chord ((a : Fin r → AddCircle (2 * Real.pi)) i) :=
        lt_of_le_of_ne (rescaledPoint_chord_nonneg _) (Ne.symm hc)
      have hcn : 0 < chord ((a : Fin r → AddCircle (2 * Real.pi)) i) ^ 2 := pow_pos h1 2
      have hp : 0 < ρ i ^ 2 := pow_pos (hρ i) 2
      exact mul_pos hp hcn
  have hne : (Finset.univ.filter (fun a : A => (a : Fin r → AddCircle (2 * Real.pi)) ≠ 0)).Nonempty :=
    ⟨⟨f, hfA⟩, by simp [hf0]⟩
  obtain ⟨b, hbmem, hbmin⟩ :=
    Finset.exists_min_image (Finset.univ.filter (fun a : A => (a : Fin r → AddCircle (2 * Real.pi)) ≠ 0))
      (fun a : A => ∑ i, ρ i ^ 2 * chord ((a : Fin r → AddCircle (2 * Real.pi)) i) ^ 2) hne
  have hb0 : (b : Fin r → AddCircle (2 * Real.pi)) ≠ 0 := (Finset.mem_filter.mp hbmem).2
  have hbA : (b : Fin r → AddCircle (2 * Real.pi)) ∈ A := b.2
  have hqb : 0 < ∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2 := hpos b hb0
  -- the minimiser does no worse than `f`
  have hbf : (∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2)
      ≤ ∑ i, ρ i ^ 2 * chord (f i) ^ 2 := by
    have hfmem : (⟨f, hfA⟩ : A) ∈
        Finset.univ.filter (fun a : A => (a : Fin r → AddCircle (2 * Real.pi)) ≠ 0) := by simp [hf0]
    have := hbmin ⟨f, hfA⟩ hfmem
    simpa using this
  have hqle : (∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2) ≤ δ ^ 2 :=
    hbf.trans hf
  -- the scaling factor and its two defining properties
  have hsq : (δ / Real.sqrt (∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2)) ^ 2
      * (∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2) = δ ^ 2 := by
    have h2 : Real.sqrt (∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2) ^ 2
        = ∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2 :=
      Real.sq_sqrt (le_of_lt hqb)
    rw [div_pow, h2]
    field_simp
  refine ⟨δ / Real.sqrt (∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2),
    ?_, (b : Fin r → AddCircle (2 * Real.pi)), hbA, hb0, ?_, ?_⟩
  · rw [le_div_iff₀ (Real.sqrt_pos.mpr hqb)]
    have h1 : Real.sqrt (∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2) ≤ δ :=
      Real.sqrt_le_iff.mpr ⟨le_of_lt hδ, hqle⟩
    linarith
  · have hmul : ∑ i,
        (δ / Real.sqrt (∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2) * ρ i) ^ 2
          * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2
        = (δ / Real.sqrt (∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2)) ^ 2
          * (∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hmul, hsq]
  · intro a haA ha0
    have hmin : (∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2)
        ≤ ∑ i, ρ i ^ 2 * chord (a i) ^ 2 := by
      have haP : (⟨a, haA⟩ : A) ∈
          Finset.univ.filter (fun a : A => (a : Fin r → AddCircle (2 * Real.pi)) ≠ 0) := by simp [ha0]
      have := hbmin ⟨a, haA⟩ haP
      simpa using this
    have hs2 : 0 < (δ / Real.sqrt (∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2)) ^ 2 := by
      have := Real.sqrt_pos.mpr hqb; positivity
    have hmul : (δ / Real.sqrt (∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2)) ^ 2
          * (∑ i, ρ i ^ 2 * chord (a i) ^ 2)
        = ∑ i, (δ / Real.sqrt (∑ i, ρ i ^ 2 * chord ((b : Fin r → AddCircle (2 * Real.pi)) i) ^ 2) * ρ i) ^ 2
          * chord (a i) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [← hmul, ← hsq]
    exact mul_le_mul_of_nonneg_left hmin (le_of_lt hs2)

end Work.Mostow
