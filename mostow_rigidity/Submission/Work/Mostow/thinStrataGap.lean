import Mathlib
import Submission.Mostow.GapADefs
import Submission.Work.Mostow.disp_blk
import Submission.Work.Mostow.blk_smul_fermi
import Submission.Work.Mostow.cosh_hdist_fermi
import Submission.Work.Mostow.fermi_inv
import Submission.Work.Mostow.conj_fundamentalDomain
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.nearId_blk
import Submission.Work.Mostow.dirichletSet_isFundamentalDomain
import Submission.Work.Mostow.exists_closest_orbit
import Submission.Work.Mostow.thinTubeDefs
import Submission.Work.Mostow.haarBridge
import Submission.Work.Mostow.ellipticAux
import Submission.Work.Mostow.tubeUnfoldStrata
import Submission.Work.Mostow.tubeQuotStrata
import Submission.Work.Mostow.geeCardK
import Submission.Work.Mostow.tubeMeasure_ball2
import Submission.Work.Mostow.geeConjCount
import Submission.Work.Mostow.cardKernelStrata
import Submission.Work.Mostow.covolLB_uncond
import Submission.Work.Mostow.dirichletSet_isFundamentalDomain
import Submission.Work.Mostow.exists_closest_orbit
import Submission.Work.Mostow.centralizer_acts_fermi
import Submission.Work.Mostow.tubeIneq
import Submission.Work.Mostow.strataAdapt
import Submission.Work.Mostow.geeArithFull
import Submission.Work.Mostow.centralizer_mem_SetStabStd
import Submission.Work.Mostow.resStd_hom_discrete
import Submission.Work.Mostow.poAction_ge1
import Submission.Work.Mostow.hypIsometry_ge1
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.resStd_hom_discrete
import Submission.Work.Mostow.resStdDiscreteStrata

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

/-! ## Bridge: `NearIdAt` at a point of the stratum bounds `rotN`

If `blk j m 1 R` moves every point of the unit ball around a point `coordEmb j m v` of the
standard stratum by less than `θ ≤ 1`, then `rotN R ≤ 2 * θ`. -/

/-- `sinh (x/2) ≤ x` for `0 < x ≤ 1`. -/
private theorem sinh_half_le_self (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) : Real.sinh (x/2) ≤ x := by
  have hy0 : 0 < 1 - x/2 := by linarith
  have key : Real.exp (x/2) ≤ 1/(1-x/2) := by
    rw [← Real.le_log_iff_exp_le (show (0:ℝ) < 1/(1-x/2) by positivity)]
    rw [Real.log_div one_ne_zero (ne_of_gt hy0), Real.log_one, zero_sub]
    have := Real.log_le_sub_one_of_pos hy0
    linarith
  have hdiv : Real.exp (x/2) ≤ (1-x/2)⁻¹ := by simpa [one_div] using key
  have key2 : Real.exp (x/2) * (1-x/2) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hdiv (le_of_lt hy0)
    rwa [inv_mul_cancel₀ (ne_of_gt hy0)] at h
  have hetwo : Real.exp (x/2) ≤ 2 := by
    have h2 : (1:ℝ)/(1-x/2) ≤ 2 := by rw [div_le_iff₀ hy0]; linarith
    linarith [key, h2]
  have h2 : 1 - x/2 ≤ Real.exp (-(x/2)) := by
    have := Real.add_one_le_exp (-(x/2)); linarith
  have h3 : Real.exp (x/2) - (1 - x/2) ≤ 2*x := by nlinarith [key2, hetwo, hx0]
  rw [Real.sinh_eq]
  linarith

/-- `fermi j m v 0 = coordEmb j m v`. -/
private theorem tsg_fermi_zero_right (j m : ℕ) (v : E j) : fermi j m v 0 = coordEmb j m v := by
  simp only [fermi, coordEmb, sinhc, norm_zero, Real.cosh_zero, one_mul]
  norm_num

/-- `hdist (coordEmb j m v) (coordEmb j m v) = 0`. -/
private theorem hdist_coordEmb_self (j m : ℕ) (v : E j) :
    hdist (coordEmb j m v) (coordEmb j m v) = 0 := by
  rw [hdist]
  have : tpart (coordEmb j m v) * tpart (coordEmb j m v)
      - inner ℝ (coordEmb j m v) (coordEmb j m v) = 1 := by
    rw [real_inner_self_eq_norm_sq, tpart]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 1 + ‖coordEmb j m v‖^2 by positivity)]
  rw [this, Real.arcosh_zero]

/-- `blk j m 1 R` fixes the stratum pointwise. -/
private theorem blk_one_smul_coordEmb (j m : ℕ) (hAj : POActionProp j) (hIj : HypIsometryProp j)
    (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (v : E j) :
    blk j m 1 R • coordEmb j m v = coordEmb j m v := by
  rw [← tsg_fermi_zero_right j m v, blk_smul_fermi j m hAj hIj hA hI (1 : PO j 1) R v 0,
    hAj.2.2.2.1 v, map_zero, tsg_fermi_zero_right]

/-- A point of height `1` above a point of the stratum is at distance `1` from it. -/
private theorem hdist_fermi_one (j m : ℕ) (hI : HypIsometryProp (j + m))
    (v : E j) (w : E m) (hw : ‖w‖ = 1) :
    hdist (fermi j m v w) (coordEmb j m v) = 1 := by
  have hdd : hdist v v = 0 := by
    rw [hdist]
    have : tpart v * tpart v - inner ℝ v v = 1 := by
      rw [real_inner_self_eq_norm_sq, tpart]
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 1 + ‖v‖^2 by positivity)]
    rw [this, Real.arcosh_zero]
  have hc := cosh_hdist_fermi j m v v w 0
  rw [tsg_fermi_zero_right j m v] at hc
  simp only [hdd, hw, norm_zero, Real.cosh_zero, mul_one, inner_zero_right, mul_zero,
    sub_zero, mul_one] at hc
  exact Real.cosh_injOn (hI.1 (fermi j m v w) (coordEmb j m v))
    (show (1:ℝ) ∈ Set.Ici (0:ℝ) by norm_num) hc

/-- **Bridge.**  `NearIdAt (blk j m 1 R) (coordEmb j m v) θ` with `θ ≤ 1` forces
`rotN R ≤ 2 * θ`. -/
theorem rotN_le_of_nearIdAt (j m : ℕ) (hAj : POActionProp j) (hIj : HypIsometryProp j)
    (hA : POActionProp (j + m)) (hI : HypIsometryProp (j + m))
    (R : E m ≃ₗᵢ[ℝ] E m) (v : E j) (θ : ℝ) (hθ1 : θ ≤ 1)
    (hN : NearIdAt (blk j m 1 R) (coordEmb j m v) θ) : rotN R ≤ 2 * θ := by
  have hAb := POBasic.ofProp hA
  have hvt : hdist (coordEmb j m v) (coordEmb j m v) = 0 := hdist_coordEmb_self j m v
  have hbvt : blk j m 1 R • coordEmb j m v = coordEmb j m v :=
    blk_one_smul_coordEmb j m hAj hIj hA hI R v
  have hθ0 : 0 < θ := by
    have h := hN (coordEmb j m v) (by rw [hvt]; norm_num)
    rwa [hbvt, hvt] at h
  have key : ∀ w : E m, ‖w‖ = 1 → ‖R w - w‖ ≤ 2 * θ := by
    intro w hw
    have hd1 : hdist (coordEmb j m v) (fermi j m v w) = 1 := by
      rw [← hdist_fermi_one j m hI v w hw]; exact hI.2.1 _ _
    have hd2 : hdist (fermi j m v w) (blk j m 1 R • fermi j m v w) < θ :=
      hN _ (le_of_eq hd1)
    have hv0 : hdist v v = 0 := (hIj.2.2.1 v v).mpr rfl
    have hdisp := disp_blk j m hAj hIj hA hI (1 : PO j 1) R v w
    rw [hAj.2.2.2.1 v, hv0, hw, inv_one, one_smul] at hdisp
    simp only [zero_div, Real.sinh_zero, mul_zero, add_zero] at hdisp
    -- `d = hdist (fermi v w) (blk ... • fermi v w)`, and `y = sinh 1 * ‖R w - w‖ / 2`
    let y : ℝ := Real.sinh 1 * ‖R w - w‖ / 2
    have hy0 : 0 ≤ y := by
      have h1 : (0:ℝ) ≤ Real.sinh 1 := le_of_lt (Real.sinh_pos_iff.mpr (by norm_num))
      simp only [y]; positivity
    have hyval : y = Real.sinh 1 * ‖R w - w‖ / 2 := rfl
    have hsq : Real.sinh (hdist (fermi j m v w) (blk j m 1 R • fermi j m v w) / 2) ^ 2
        = y ^ 2 := by
      rw [hdisp, hyval]; ring
    have hnnf : (0:ℝ) ≤ hdist (fermi j m v w) (blk j m 1 R • fermi j m v w) := hI.1 _ _
    have hdnn : 0 ≤ Real.sinh (hdist (fermi j m v w) (blk j m 1 R • fermi j m v w) / 2) :=
      Real.sinh_nonneg_iff.mpr (by linarith)
    have heq : Real.sinh (hdist (fermi j m v w) (blk j m 1 R • fermi j m v w) / 2) = y := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · exact h
      · rw [h]; linarith
    have hd_eq : hdist (fermi j m v w) (blk j m 1 R • fermi j m v w) = 2 * Real.arsinh y := by
      have h2 : Real.arsinh (Real.sinh
          (hdist (fermi j m v w) (blk j m 1 R • fermi j m v w) / 2))
          = hdist (fermi j m v w) (blk j m 1 R • fermi j m v w) / 2 := Real.arsinh_sinh _
      rw [heq] at h2
      linarith [h2]
    have hlt : y < θ := by
      rcases lt_or_eq_of_le hy0 with hypos | hyzero
      · by_cases hy1 : y ≤ 1
        · have hsh : Real.sinh (y/2) ≤ y := sinh_half_le_self y hypos hy1
          have hle : y/2 ≤ Real.arsinh y := by
            rw [← Real.arsinh_sinh (y/2)]
            exact (Real.arsinh_le_arsinh).mpr hsh
          linarith [hd2, hd_eq]
        · exfalso
          have hy1' : 1 < y := not_le.mp hy1
          have h1 : Real.arsinh 1 < Real.arsinh y := (Real.arsinh_lt_arsinh).mpr hy1'
          have h2 : (1:ℝ)/2 ≤ Real.arsinh 1 := by
            have h3 : Real.sinh (1/2) ≤ 1 := sinh_half_le_self 1 (by norm_num) (by norm_num)
            rw [← Real.arsinh_sinh (1/2)]
            exact (Real.arsinh_le_arsinh).mpr h3
          linarith [hd2, hd_eq, hθ1, h1, h2]
      · rw [← hyzero]; exact hθ0
    have hnorm : ‖R w - w‖ = 2 * y / Real.sinh 1 := by
      rw [hyval]
      have hs1 : Real.sinh 1 ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr (by norm_num))
      field_simp
    rw [hnorm]
    have hs1 : 1 ≤ Real.sinh 1 := (Real.self_le_sinh_iff).mpr (by norm_num)
    have hpos : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr (by norm_num)
    rw [div_le_iff₀ hpos]
    nlinarith [hlt, hθ0, hs1, hy0]
  exact nib_rotN_le_of_unit (by linarith) key


/-- Every discrete subgroup of `PO N 1` admits a `volH N`-fundamental domain: take the Dirichlet
domain at a point with trivial stabiliser.  (The `N = 3` case is
`Work.Mostow.gapA.exists_fundamentalDomain`.) -/
theorem exists_fundamentalDomain_gen (N : ℕ) (hA : POActionProp N) (hI : HypIsometryProp N)
    (H : Subgroup (PO N 1)) (hdisc : IsDiscrete (SetLike.coe H)) :
    ∃ D : Set (E N), IsFundamentalDomain H D (volH N) := by
  haveI : Countable ↥H := countable_of_isDiscrete (PO N 1) hdisc
  obtain ⟨o, ho⟩ := exists_trivial_stabiliser N hA hI H hdisc
  exact ⟨dirichletSet H o, dirichletSet_isFundamentalDomain N hA hI H o ho
    (fun x => exists_closest_orbit N hA hI hdisc o x)⟩

/-!
## Structure of the proof of `thinStrataGap` (current state; read this first)

### !!! IMPORT-CYCLE TRAP !!!
`Submission/Work/Mostow/geeGoodTube.lean` **imports this file** (it uses
`Work.Mostow.exists_fundamentalDomain_gen`).  Hence `thinStrataGap.lean` must NOT import
`geeGoodTube`, `strataGoodCase`, `geeThinStrataGap`, `geodStratumOddProved`, `ftbStandardTube`,
`torsionNearIdGeodesic`, `gapAEvenEngine`, `strataGapUniform` — anything that transitively imports
`thinStrataGap` (check with
`grep -rl "import Submission.Work.Mostow.thinStrataGap" Submission/`).  Importing one of them makes
the file fail with a flood of "declaration has already been declared".  (This is why the
fixed-free stratum case is reproved here as `tsg_goodInline` instead of reusing the proved
`Work.Mostow.strataGoodCase`.)

### PROVED in this file
* `rotN_le_of_nearIdAt` — **the bridge**: `NearIdAt (blk j m 1 R) (coordEmb j m v) θ`, `θ ≤ 1`,
  gives `rotN R ≤ 2 θ` (test point at Fermi height `1`; `Work.Mostow.disp_blk`; the elementary
  inequality `sinh (x/2) ≤ x` for `0 < x ≤ 1`).  (Imported by `geeGoodTube.lean` — do not move or
  rename it.)
* `exists_fundamentalDomain_gen` — every discrete subgroup of `PO N 1` has a Dirichlet fundamental
  domain.  (Also imported by `geeGoodTube.lean`.)
* `fixSet_blk_eq_stdTG` — `R` fixed-free ⟹ `fixSet (blk k m 1 R) = stdTG k m`.
* transports along an equality of ambient dimensions, each by `cases e`: `tsg_volH_cast`,
  `tsg_isDiscrete_cast`, `tsg_isFundamentalDomain_cast`, `tsg_mem_cast`, `tsg_mem_cast'`,
  `tsg_cast_cast_po`, `tsg_cast_ne_one`, and the separation transfer `tsg_sep_cast`.
* `exists_min_pointwiseStab` — the non-identity element of `Λ` fixing `stdTG k m` pointwise whose
  normal part has minimal `rotN` (the pointwise stabiliser is finite because its elements fix
  `0 = coordEmb k m 0`).
* `tsg_goodInline` — the **fixed-free stratum case** for one split `(j, m)`, self-contained:
  `∃ c α > 0` such that `Λ` discrete, `D` a fundamental domain, `blk j m 1 R ∈ Λ` with `R`
  fixed-free, separation hypothesis, `rotN R ≤ 2 θ`, `θ ∈ (0,1]` imply
  `ofReal (c * θ ^ (-α)) ≤ volH (j+m) D`.  Proof: `Work.Mostow.tubeIneq` +
  `Work.Mostow.tubeMeasure_ball2` + `Work.Mostow.geeCardK` + `Work.Mostow.covolLB_uncond` +
  `Work.Mostow.geeArithFull` (all safe), with `α = 1`; the case `rotN R > κ₀ := min 1 (η₁/(2 sinh 2))`
  is handled by the unconditional covolume bound `Work.Mostow.covolLB_uncond`, and the two constants
  are combined with a `min`.
* `strataMaster` — **the master statement**: uniformly over all admissible splits of `n` (finite
  set `tsg_splits n`), a fixed-free block element with `rotN R ≤ 2θ` and the separation hypothesis
  gives `ofReal (C * θ ^ (-A)) ≤ volH n D` for constants `C, A > 0` independent of the split.  This
  is `tsg_goodInline` combined over the finitely many splits with `Finset.min'`.
* `thinStrataGap_of_adapt` — the whole assembly, taking the stratum-adaptation lemma
  (`TsgAdapt`, the statement of `Work.Mostow.strataAdapt`) as a hypothesis: the `rotN`-minimal
  element `R₀` of the pointwise stabiliser is chosen; if it is fixed-free the master statement is
  applied at the split `(k, m)`, otherwise the adaptation moves to the split `(j', m')` of its fixed
  stratum and the master statement is applied there (`volH` is preserved by the adaptation).

### REMAINING
* `Work.Mostow.strataAdapt` (`Submission/Work/Mostow/strataAdapt.lean`, being proved in parallel):
  the configuration transport to the split of the fixed stratum of `blk k m 1 S` when `S` has a
  nonzero fixed vector.
* `thinStrataGap` = `thinStrataGap_of_adapt n hn (fun k m hk hm => strataAdapt k m hk hm)`.

### Also available and safe (do not import the unsafe list above)
`Work.Mostow.covolLB_uncond (N) (hN : 2 ≤ N) : CovolLB N` (**Kazhdan–Margulis in every dimension
`≥ 2`, unconditionally**, in `Submission/Work/Mostow/covolLB_uncond.lean`), and the earlier pieces
`tubeUnfoldStrata`, `tubeQuotStrata`, `cardKernelStrata`, `cardKernelTorus`, `resStdDiscreteStrata`.
-/

/-- If `R` has no fixed vector then the fixed set of `blk k m 1 R` is exactly the standard
stratum `stdTG k m`. -/
theorem fixSet_blk_eq_stdTG (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m)) (R : E m ≃ₗᵢ[ℝ] E m)
    (hR : ∀ w, R w = w → w = 0) : fixSet (blk k m 1 R) = stdTG k m := by
  ext u
  constructor
  · intro hu
    obtain ⟨v, w, rfl⟩ : ∃ v w, u = fermi k m v w := ⟨_, _, (fermi_inv k m).2.1 u |>.symm⟩
    have huw : blk k m 1 R • fermi k m v w = fermi k m v w := hu
    rw [blk_smul_fermi k m hAk hIk hA hI 1 R v w, hAk.2.2.2.1 v] at huw
    have h2 := congrArg (fermiInv k m) huw
    rw [(fermi_inv k m).1 v (R w), (fermi_inv k m).1 v w] at h2
    have hw : R w = w := (Prod.ext_iff.mp h2).2
    have hw0 : w = 0 := hR w hw
    refine ⟨v, ?_⟩
    rw [← tsg_fermi_zero_right k m v, hw0]
  · rintro ⟨v, rfl⟩
    show blk k m 1 R • coordEmb k m v = coordEmb k m v
    rw [← tsg_fermi_zero_right k m v, blk_smul_fermi k m hAk hIk hA hI 1 R v 0,
      hAk.2.2.2.1 v, LinearIsometryEquiv.map_zero, tsg_fermi_zero_right k m v]

/-! ## Transports along an equality of ambient dimensions

All four are proved by `cases e`, which collapses the cast; they are the tools that let the
"master" statement below be stated in the ambient dimension while the per-split lemmas live in
`PO (j + m) 1`. -/

private theorem tsg_volH_cast {a b : ℕ} (e : a = b) (s : Set (E a)) : volH b (e ▸ s) = volH a s := by
  cases e; rfl

private theorem tsg_isDiscrete_cast {a b : ℕ} (e : a = b) (Λ : Subgroup (PO b 1)) :
    IsDiscrete (Λ : Set (PO b 1)) → IsDiscrete ((e.symm ▸ Λ : Subgroup (PO a 1)) : Set (PO a 1)) := by
  cases e; exact id

private theorem tsg_isFundamentalDomain_cast {a b : ℕ} (e : a = b) (Λ : Subgroup (PO b 1))
    (D : Set (E b)) :
    IsFundamentalDomain Λ D (volH b) →
      IsFundamentalDomain (e.symm ▸ Λ : Subgroup (PO a 1)) (e.symm ▸ D) (volH a) := by
  cases e; exact id

private theorem tsg_mem_cast {a b : ℕ} (e : a = b) (Λ : Subgroup (PO b 1)) (x : PO a 1) :
    (e ▸ x : PO b 1) ∈ Λ → x ∈ (e.symm ▸ Λ : Subgroup (PO a 1)) := by
  cases e; exact id

private theorem tsg_mem_cast' {a b : ℕ} (e : a = b) (Λ : Subgroup (PO b 1)) (x : PO a 1) :
    x ∈ (e.symm ▸ Λ : Subgroup (PO a 1)) → (e ▸ x : PO b 1) ∈ Λ := by
  cases e; exact id

private theorem tsg_cast_cast_po {a b : ℕ} (e : a = b) (X : PO a 1) :
    (e.symm ▸ (e ▸ X) : PO a 1) = X := by
  cases e; rfl

private theorem tsg_cast_ne_one {a b : ℕ} (e : a = b) (X : PO a 1) :
    ((e ▸ X : PO b 1) = 1) ↔ X = 1 := by
  cases e; rfl

/-- The separation hypothesis of `Work.Mostow.strataGoodCase`, transported from the ambient
`PO N 1` (with the element written as the cast `e ▸ blk j m 1 R`) to the split `PO (j + m) 1`. -/
private theorem tsg_sep_cast {j m N : ℕ} (e : j + m = N) (Λ : Subgroup (PO N 1))
    (R : E m ≃ₗᵢ[ℝ] E m)
    (h : ∀ c : PO N 1, c ∈ Λ → c ∈ Subgroup.centralizer {(e ▸ blk j m 1 R : PO N 1)} →
      resStd j m (e.symm ▸ c : PO (j + m) 1) = 1 → c ≠ 1 →
      rotN R ≤ rotN (nrmStd j m (e.symm ▸ c : PO (j + m) 1))) :
    ∀ c₁ : PO (j + m) 1, c₁ ∈ (e.symm ▸ Λ : Subgroup (PO (j + m) 1)) →
      c₁ ∈ Subgroup.centralizer {blk j m 1 R} → resStd j m c₁ = 1 → c₁ ≠ 1 →
      rotN R ≤ rotN (nrmStd j m c₁) := by
  intro c₁ hmem hcen hrs hne
  have hmem' : (e ▸ c₁ : PO N 1) ∈ Λ := tsg_mem_cast' e Λ c₁ hmem
  have hcen' : (e ▸ c₁ : PO N 1) ∈ Subgroup.centralizer {(e ▸ blk j m 1 R : PO N 1)} := by
    rw [Subgroup.mem_centralizer_iff] at hcen ⊢
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have h1 : blk j m 1 R * c₁ = c₁ * blk j m 1 R := hcen (blk j m 1 R) (Set.mem_singleton _)
    have h2 : (e ▸ (c₁ * blk j m 1 R) : PO N 1) = e ▸ (blk j m 1 R * c₁) := by rw [h1]
    rw [cast_mul_po, cast_mul_po] at h2
    exact h2.symm
  have hres' : resStd j m ((e.symm ▸ (e ▸ c₁) : PO (j + m) 1)) = 1 := by
    rw [tsg_cast_cast_po e c₁]; exact hrs
  have hne' : (e ▸ c₁ : PO N 1) ≠ 1 := fun hc => hne ((tsg_cast_ne_one e c₁).mp hc)
  have hres := h (e ▸ c₁) hmem' hcen' hres' hne'
  rwa [tsg_cast_cast_po e c₁] at hres

/-- `rotN 1 = 0`. -/
private theorem tsg_rotN_one {m : ℕ} : rotN (1 : E m ≃ₗᵢ[ℝ] E m) = 0 := by
  rw [rotN, norm_eq_zero]
  ext x
  simp

/-- A linear isometry equivalence of operator distance `0` from the identity is the identity. -/
private theorem tsg_rotN_eq_zero {m : ℕ} (R : E m ≃ₗᵢ[ℝ] E m) (h : rotN R = 0) : R = 1 := by
  have h1 : (R.toLinearIsometry.toContinuousLinearMap - ContinuousLinearMap.id ℝ (E m)) = 0 :=
    norm_eq_zero.mp h
  refine LinearIsometryEquiv.ext (fun x => ?_)
  have h2 := congrArg (fun (f : E m →L[ℝ] E m) => f x) h1
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.zero_apply] at h2
  exact sub_eq_zero.mp h2

/-- `blk k m 1 R` lies in the setwise stabiliser of the standard stratum. -/
private theorem tsg_blk_mem_SetStabStd (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m)) (R : E m ≃ₗᵢ[ℝ] E m) :
    blk k m 1 R ∈ SetStabStd k m := by
  intro u
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, (blk_one_smul_coordEmb k m hAk hIk hA hI R v).symm⟩
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    have hinvfix : (blk k m 1 R)⁻¹ • coordEmb k m v = coordEmb k m v := by
      have h := congrArg (fun w => (blk k m 1 R)⁻¹ • w)
        (blk_one_smul_coordEmb k m hAk hIk hA hI R v)
      rw [← (hA.2.2.2.2.1 (blk k m 1 R)⁻¹ (blk k m 1 R) (coordEmb k m v)), inv_mul_cancel,
        hA.2.2.2.1] at h
      exact h.symm
    have h1 : u = (blk k m 1 R)⁻¹ • ((blk k m 1 R) • u) := by
      rw [← (hA.2.2.2.2.1 (blk k m 1 R)⁻¹ (blk k m 1 R) u), inv_mul_cancel, hA.2.2.2.1]
    have h2 : (blk k m 1 R)⁻¹ • ((blk k m 1 R) • u) = coordEmb k m v := by
      rw [← hv, hinvfix]
    exact (h1.trans h2).symm

/-- The normal part of `blk k m 1 R` is `R`. -/
private theorem tsg_nrmStd_blk (k m : ℕ) (hAk : POActionProp k) (hIk : HypIsometryProp k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m)) (R : E m ≃ₗᵢ[ℝ] E m) :
    nrmStd k m (blk k m 1 R) = R :=
  ((blk_hom k m hAk hIk hA hI).2.2 _ _ _ _
    (rhd_stab_eq_blk k m hAk hIk hA hI (blk k m 1 R)
      (tsg_blk_mem_SetStabStd k m hAk hIk hA hI R))).2.symm

/-! ## The `rotN`-minimal element of the pointwise stabiliser of the stratum -/

/-- Among the non-identity elements of `Λ` that fix `stdTG k m` pointwise there is one whose normal
part has minimal `rotN`.  (The pointwise stabiliser is finite: its elements fix the base point
`coordEmb k m 0 = 0`.) -/
theorem exists_min_pointwiseStab (k m : ℕ) (hk : 2 ≤ k)
    (hA : POActionProp (k + m)) (hI : HypIsometryProp (k + m))
    (Λ : Subgroup (PO (k + m) 1)) (hdisc : IsDiscrete (Λ : Set (PO (k + m) 1)))
    (R : E m ≃ₗᵢ[ℝ] E m) (hb : blk k m 1 R ∈ Λ) (hR : 0 < rotN R) :
    ∃ R₀ : E m ≃ₗᵢ[ℝ] E m, 0 < rotN R₀ ∧ rotN R₀ ≤ rotN R ∧ blk k m 1 R₀ ∈ Λ ∧
      (∀ c : PO (k + m) 1, c ∈ Λ → (∀ v : E k, c • coordEmb k m v = coordEmb k m v) → c ≠ 1 →
        rotN R₀ ≤ rotN (nrmStd k m c)) := by
  classical
  have hAk : POActionProp k := poAction_ge1 k (by omega)
  have hIk : HypIsometryProp k := hypIsometry_ge1 k (by omega) hAk
  have hAb : POBasic (k + m) := POBasic.ofProp hA
  have hIb : HypIsoData (k + m) := HypIsoData.ofProp hI
  have hzero : hdist (0 : E (k + m)) (0 : E (k + m)) = 0 := (hI.2.2.1 _ _).mpr rfl
  -- the finite set of elements fixing the stratum pointwise
  set P : Set (PO (k + m) 1) :=
    {c | c ∈ Λ ∧ ∀ v : E k, c • coordEmb k m v = coordEmb k m v} with hPdef
  have hPfin : P.Finite := by
    refine ((finite_nearStab hAb hIb hdisc 1).image Subtype.val).subset ?_
    rintro c ⟨hcΛ, hcfix⟩
    refine ⟨⟨c, hcΛ⟩, ?_, rfl⟩
    have hc0 : (⟨c, hcΛ⟩ : Λ) • (0 : E (k + m)) = 0 := by
      rw [← rhd_coordEmb_zero k m]
      exact hcfix 0
    show hdist 0 ((⟨c, hcΛ⟩ : Λ) • (0 : E (k + m))) ≤ 1
    rw [hc0, hzero]; norm_num
  have hbP : blk k m 1 R ∈ P :=
    ⟨hb, fun v => blk_one_smul_coordEmb k m hAk hIk hA hI R v⟩
  have hbne : blk k m 1 R ≠ 1 := by
    intro h
    have hR1 : R = 1 := ((blk_hom k m hAk hIk hA hI).2.2 _ _ _ _
      (h.trans (blk_hom k m hAk hIk hA hI).2.1.symm)).2
    rw [hR1, tsg_rotN_one] at hR
    exact lt_irrefl _ hR
  have hTne : (hPfin.toFinset.erase (1 : PO (k + m) 1)).Nonempty := by
    refine ⟨blk k m 1 R, ?_⟩
    rw [Finset.mem_erase]
    exact ⟨hbne, (hPfin.mem_toFinset).mpr hbP⟩
  obtain ⟨b₀, hb₀T, hb₀min⟩ := Finset.exists_min_image
    (hPfin.toFinset.erase (1 : PO (k + m) 1)) (fun c => rotN (nrmStd k m c)) hTne
  have hb₀P : b₀ ∈ P := (hPfin.mem_toFinset).mp (Finset.mem_of_mem_erase hb₀T)
  have hb₀ne : b₀ ≠ 1 := (Finset.mem_erase.mp hb₀T).1
  have hb₀Λ : b₀ ∈ Λ := hb₀P.1
  have hb₀fix : ∀ v : E k, b₀ • coordEmb k m v = coordEmb k m v := hb₀P.2
  have hb₀stab : b₀ ∈ SetStabStd k m := by
    intro u
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, (hb₀fix v).symm⟩
    · rintro ⟨v, hv⟩
      refine ⟨v, ?_⟩
      have hinvfix : b₀⁻¹ • coordEmb k m v = coordEmb k m v := by
        have h := congrArg (fun w => b₀⁻¹ • w) (hb₀fix v)
        rw [← (hA.2.2.2.2.1 b₀⁻¹ b₀ (coordEmb k m v)), inv_mul_cancel, hA.2.2.2.1] at h
        exact h.symm
      have h1 : u = b₀⁻¹ • (b₀ • u) := by
        rw [← (hA.2.2.2.2.1 b₀⁻¹ b₀ u), inv_mul_cancel, hA.2.2.2.1]
      have h2 : b₀⁻¹ • (b₀ • u) = coordEmb k m v := by
        rw [← hv, hinvfix]
      exact (h1.trans h2).symm
  have hb₀res : resStd k m b₀ = 1 := by
    refine hAk.2.2.2.2.2.1 _ (fun v => ?_)
    have h1 : coordEmb k m (resStd k m b₀ • v) = coordEmb k m v := by
      rw [← rhd_resStd_smul_coordEmb k m hAk hIk hA hI hb₀stab v]
      exact hb₀fix v
    exact RdsAux.coordEmb_injective k m h1
  have hb₀form : b₀ = blk k m 1 (nrmStd k m b₀) := by
    conv_lhs => rw [rhd_stab_eq_blk k m hAk hIk hA hI b₀ hb₀stab]
    rw [hb₀res]
  refine ⟨nrmStd k m b₀, ?_, ?_, ?_, ?_⟩
  · have hle : 0 ≤ rotN (nrmStd k m b₀) := by rw [rotN]; exact norm_nonneg _
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exfalso
      have hR1 : nrmStd k m b₀ = 1 := tsg_rotN_eq_zero _ h.symm
      have hb₀one : b₀ = 1 := by rw [hb₀form, hR1, (blk_hom k m hAk hIk hA hI).2.1]
      exact hb₀ne hb₀one
  · have hbT : blk k m 1 R ∈ hPfin.toFinset.erase (1 : PO (k + m) 1) := by
      rw [Finset.mem_erase]
      exact ⟨hbne, (hPfin.mem_toFinset).mpr hbP⟩
    have := hb₀min (blk k m 1 R) hbT
    rwa [tsg_nrmStd_blk k m hAk hIk hA hI R] at this
  · rw [← hb₀form]
    exact hb₀Λ
  · intro c hcΛ hcfix hcne
    have hcP : c ∈ P := ⟨hcΛ, hcfix⟩
    have hcT : c ∈ hPfin.toFinset.erase (1 : PO (k + m) 1) := by
      rw [Finset.mem_erase]
      exact ⟨hcne, (hPfin.mem_toFinset).mpr hcP⟩
    exact hb₀min c hcT

/-! ## The set of admissible splits and the "master" statement -/

/-- The admissible splits of `n`: `(j, n - j)` for `2 ≤ j ≤ n - 1`, i.e. `j + m = n`, `2 ≤ j`
(stratum dimension at least `2`) and `1 ≤ m` (normal dimension at least `1`). -/
private def tsg_splits (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 2 (n - 1)).image (fun j => (j, n - j))

private theorem tsg_mem_splits {n : ℕ} {p : ℕ × ℕ} :
    p ∈ tsg_splits n ↔ p.1 + p.2 = n ∧ 2 ≤ p.1 ∧ 1 ≤ p.2 := by
  unfold tsg_splits
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_Icc] at hj
    exact ⟨by omega, hj.1, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨p.1, by rw [Finset.mem_Icc]; omega, ?_⟩
    ext <;> simp <;> omega

/-- The conclusion of the per-split lemma `thinStrataGood` for the split `p`. -/
private abbrev TsgGood (p : ℕ × ℕ) (c α : ℝ) : Prop :=
  ∀ (Λ : Subgroup (PO (p.1 + p.2) 1)) (D : Set (E (p.1 + p.2))) (R : E p.2 ≃ₗᵢ[ℝ] E p.2)
    (θ : ℝ),
    IsDiscrete (Λ : Set (PO (p.1 + p.2) 1)) → IsFundamentalDomain Λ D (volH (p.1 + p.2)) →
    blk p.1 p.2 1 R ∈ Λ → (∀ w : E p.2, R w = w → w = 0) → 0 < rotN R →
    rotN R ≤ 2 * θ → 0 < θ → θ ≤ 1 →
    (∀ c : PO (p.1 + p.2) 1, c ∈ Λ → c ∈ Subgroup.centralizer {blk p.1 p.2 1 R} →
      resStd p.1 p.2 c = 1 → c ≠ 1 → rotN R ≤ rotN (nrmStd p.1 p.2 c)) →
    ENNReal.ofReal (c * θ ^ (-α)) ≤ volH (p.1 + p.2) D

/-! ## The self-contained "good case" for one split

`Work.Mostow.geeGoodTube` proves this same statement but lives in a module that imports
`thinStrataGap`, so it cannot be used here (import cycle).  The proof below is assembled from
`Work.Mostow.tubeIneq`, `Work.Mostow.covolLB_uncond`, `Work.Mostow.geeCardK`,
`Work.Mostow.tubeMeasure_ball2` and `Work.Mostow.geeArithFull`, none of which depend on
`thinStrataGap`.

Compared with `geeGoodTube` there is no threshold hypothesis: the case `rotN R > κ₀` is handled by
the unconditional covolume bound `covolLB_uncond`, and the two constants are combined with a `min`.
The exponent is `α = 1` throughout. -/

/-- A subset of a discrete set is discrete. -/
private lemma tsg_isDiscrete_subset {X : Type*} [TopologicalSpace X] {s t : Set X}
    (ht : IsDiscrete t) (h : s ⊆ t) : IsDiscrete s := by
  rw [isDiscrete_iff_nhdsNE] at ht ⊢
  intro x hx
  have hle : nhdsWithin x ({x}ᶜ) ⊓ Filter.principal s ≤
      nhdsWithin x ({x}ᶜ) ⊓ Filter.principal t :=
    inf_le_inf le_rfl (Filter.principal_mono.mpr h)
  rw [ht x (h hx)] at hle
  exact le_bot_iff.mp hle

private theorem tsg_goodInline (j m : ℕ) (hj : 2 ≤ j) (hm : 1 ≤ m) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧ TsgGood (j, m) c α := by
  classical
  have hAj : POActionProp j := poAction_ge1 j (by omega)
  have hIj : HypIsometryProp j := hypIsometry_ge1 j (by omega) hAj
  have hA : POActionProp (j + m) := poAction_ge1 (j + m) (by omega)
  have hI : HypIsometryProp (j + m) := hypIsometry_ge1 (j + m) (by omega) hA
  obtain ⟨η₁, hη₁, Cn, hCn, htubeI⟩ := tubeIneq j m hAj hIj hA hI
  obtain ⟨v, hv, hCov⟩ := covolLB_uncond j hj
  obtain ⟨vN, hvN, hCovN⟩ := covolLB_uncond (j + m) (by omega)
  obtain ⟨CK, hCK, hK⟩ := geeCardK j m hAj hIj hA hI
  obtain ⟨c₁, c₂, hc₁, hc₂, hball⟩ := tubeMeasure_ball2 j m hm (by omega : 2 ≤ j + m)
  set N : ℕ := j + m - 1 with hNdef
  have hNcast : ((j + m : ℕ) - 1 : ℝ) = (N : ℝ) := by
    rw [hNdef]; push_cast [Nat.cast_sub (by omega : 1 ≤ j + m)]; ring
  have hNge : 1 + (m : ℝ) / 2 ≤ (N : ℝ) := by
    rw [hNcast.symm]
    have h1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (by omega : 1 ≤ j)
    have h2 : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    push_cast [Nat.cast_sub (by omega : 1 ≤ j + m)]
    linarith
  have hsinh2 : 0 < Real.sinh 2 := Real.sinh_pos_iff.mpr (by norm_num)
  have hκ0pos : 0 < min 1 (η₁ / (2 * Real.sinh 2)) := lt_min one_pos (by positivity)
  set cT : ℝ := v * c₁ * Real.exp (-(N : ℝ)) * η₁ ^ N / (Cn * CK) with hcTdef
  have hcTpos : 0 < cT := by
    rw [hcTdef]
    exact div_pos (mul_pos (mul_pos (mul_pos hv hc₁) (Real.exp_pos _)) (pow_pos hη₁ N))
      (mul_pos hCn hCK)
  set cK : ℝ := vN * (min 1 (η₁ / (2 * Real.sinh 2)) / 2) with hcKdef
  have hcKpos : 0 < cK := by rw [hcKdef]; exact mul_pos hvN (by positivity)
  refine ⟨min (cT / 2) cK, 1, lt_min (by positivity) hcKpos, one_pos, ?_⟩
  intro Λ D R θ hdisc hD hb hRnfix hRpos hR2θ hθ0 hθ1 hsep
  by_cases hsmall : rotN R ≤ min 1 (η₁ / (2 * Real.sinh 2))
  · -- ### the tube branch
    have hCc : Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ⊓ Λ ≤ Λ := fun x hx =>
      (Subgroup.mem_inf.mp hx).2
    let Cc : Subgroup (PO (j + m) 1) :=
      Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ⊓ Λ
    let ΓY : Subgroup (PO j 1) :=
      Subgroup.closure (resStd j m '' (Cc : Set (PO (j + m) 1)))
    have hCcdisc : IsDiscrete (SetLike.coe Cc) := tsg_isDiscrete_subset hdisc hCc
    have hCcstab : ∀ c ∈ Cc, c ∈ SetStabStd j m := fun c hc =>
      centralizer_mem_SetStabStd j m hAj hIj hA hI R hRnfix c (Subgroup.mem_inf.mp hc).1
    have hΓYdisc : IsDiscrete (SetLike.coe ΓY) :=
      ((resStd_hom_discrete j m hAj hIj hA hI).2 Cc hCcdisc hCcstab).1
    obtain ⟨DY, hDY⟩ := exists_fundamentalDomain_gen j hAj hIj ΓY hΓYdisc
    set ρ : ℝ := Real.arsinh (η₁ / (2 * rotN R)) - 1 with hρdef
    have hθκ' : rotN R ≤ η₁ / (2 * Real.sinh 2) := le_trans hsmall (min_le_right _ _)
    have hθle1 : rotN R ≤ 1 := le_trans hsmall (min_le_left _ _)
    have hkey : 2 * Real.sinh 2 * rotN R ≤ η₁ := by
      have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sinh 2)).mp hθκ'
      linarith
    have hxge : Real.sinh 2 ≤ η₁ / (2 * rotN R) :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * rotN R)).mpr (by linarith)
    have harsinh : (2 : ℝ) ≤ Real.arsinh (η₁ / (2 * rotN R)) :=
      calc (2 : ℝ) = Real.arsinh (Real.sinh 2) := (Real.arsinh_sinh 2).symm
        _ ≤ Real.arsinh (η₁ / (2 * rotN R)) := Real.arsinh_le_arsinh.mpr hxge
    have hρ1 : 1 ≤ ρ := by rw [hρdef]; linarith
    have hρ0 : 0 ≤ ρ := le_trans zero_le_one hρ1
    have htubec : 2 * Real.sinh (ρ + 1) * rotN R ≤ η₁ := by
      have h1 : ρ + 1 = Real.arsinh (η₁ / (2 * rotN R)) := by rw [hρdef]; ring
      rw [h1, Real.sinh_arsinh]
      field_simp
      linarith
    have hmain : volH j DY * tubeMeasure j m (Metric.closedBall 0 ρ) ≤
        ENNReal.ofReal Cn *
          (Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk j m 1 R} ∧
            resStd j m c = 1} : ENNReal) * volH (j + m) D :=
      htubeI Λ D hdisc hD R hb hRnfix DY hDY ρ hρ0 htubec
    have hKcard := hK Λ R (rotN R) hdisc hb hRnfix hRpos le_rfl hsep
    have hDYlb : ENNReal.ofReal v ≤ volH j DY := hCov ΓY hΓYdisc DY hDY
    have htmLb : ENNReal.ofReal (c₁ * Real.exp ((N : ℝ) * ρ)) ≤
        tubeMeasure j m (Metric.closedBall 0 ρ) := by
      have h := (hball ρ hρ1).1
      rwa [hNcast] at h
    have hstep : ENNReal.ofReal v * ENNReal.ofReal (c₁ * Real.exp ((N : ℝ) * ρ)) ≤
        volH j DY * tubeMeasure j m (Metric.closedBall 0 ρ) :=
      mul_le_mul' hDYlb htmLb
    have hchain : ENNReal.ofReal (v * (c₁ * Real.exp ((N : ℝ) * ρ))) ≤
        ENNReal.ofReal (Cn * (CK * (rotN R) ^ (-(m : ℝ) / 2))) * volH (j + m) D := by
      have h1 : ENNReal.ofReal (v * (c₁ * Real.exp ((N : ℝ) * ρ)))
          = ENNReal.ofReal v * ENNReal.ofReal (c₁ * Real.exp ((N : ℝ) * ρ)) :=
        ENNReal.ofReal_mul (le_of_lt hv)
      have h2 : ENNReal.ofReal Cn * ENNReal.ofReal (CK * (rotN R) ^ (-(m : ℝ) / 2))
          = ENNReal.ofReal (Cn * (CK * (rotN R) ^ (-(m : ℝ) / 2))) :=
        (ENNReal.ofReal_mul (le_of_lt hCn)).symm
      rw [h1, ← h2]
      exact le_trans hstep (le_trans hmain
        (mul_le_mul' (mul_le_mul' (le_refl _) hKcard) (le_refl _)))
    have hqpos : 0 < Cn * (CK * (rotN R) ^ (-(m : ℝ) / 2)) :=
      mul_pos hCn (mul_pos hCK (Real.rpow_pos_of_pos hRpos _))
    have hpq : ENNReal.ofReal ((v * (c₁ * Real.exp ((N : ℝ) * ρ))) /
          (Cn * (CK * (rotN R) ^ (-(m : ℝ) / 2)))) ≤ volH (j + m) D := by
      rw [ENNReal.ofReal_div_of_pos hqpos]
      refine (ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hqpos))
        ENNReal.ofReal_ne_top).mpr ?_
      calc ENNReal.ofReal (v * (c₁ * Real.exp ((N : ℝ) * ρ)))
          ≤ ENNReal.ofReal (Cn * (CK * (rotN R) ^ (-(m : ℝ) / 2))) * volH (j + m) D := hchain
        _ = volH (j + m) D * ENNReal.ofReal (Cn * (CK * (rotN R) ^ (-(m : ℝ) / 2))) :=
            mul_comm _ _
    have harith := geeArithFull N m v c₁ η₁ Cn CK (rotN R) ρ hv hc₁ hη₁ hCn hCK hRpos hθle1
      hNge hρdef
    have htube : ENNReal.ofReal (cT * (rotN R) ^ (-1 : ℝ)) ≤ volH (j + m) D := by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hpq
      rw [hcTdef]
      exact harith
    -- convert `(rotN R)^{-1}` into `θ^{-1}`
    have hinv : (2 * θ) ^ (-1 : ℝ) ≤ (rotN R) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, Real.rpow_neg_one]
      exact (inv_le_inv₀ (by linarith) hRpos).mpr hR2θ
    have hconv : min (cT / 2) cK * θ ^ (-1 : ℝ) ≤ cT * (rotN R) ^ (-1 : ℝ) := by
      have h1 : min (cT / 2) cK ≤ cT / 2 := min_le_left _ _
      have h2 : (0 : ℝ) ≤ θ ^ (-1 : ℝ) := (Real.rpow_pos_of_pos hθ0 _).le
      have h3 : (cT / 2) * θ ^ (-1 : ℝ) ≤ cT * (rotN R) ^ (-1 : ℝ) := by
        have h4 : (2 * θ) ^ (-1 : ℝ) = (2 : ℝ)⁻¹ * θ ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one, Real.rpow_neg_one, mul_inv]
        calc (cT / 2) * θ ^ (-1 : ℝ) = cT * ((2 : ℝ)⁻¹ * θ ^ (-1 : ℝ)) := by ring
          _ = cT * (2 * θ) ^ (-1 : ℝ) := by rw [h4]
          _ ≤ cT * (rotN R) ^ (-1 : ℝ) := by
              exact mul_le_mul_of_nonneg_left hinv (le_of_lt hcTpos)
      calc min (cT / 2) cK * θ ^ (-1 : ℝ)
          ≤ (cT / 2) * θ ^ (-1 : ℝ) := mul_le_mul_of_nonneg_right h1 h2
        _ ≤ cT * (rotN R) ^ (-1 : ℝ) := h3
    exact le_trans (ENNReal.ofReal_le_ofReal hconv) htube
  · -- ### the covolume branch: `rotN R` is large, so `θ` is large
    push_neg at hsmall
    have hκ0le : min 1 (η₁ / (2 * Real.sinh 2)) < rotN R := hsmall
    have hthalf : min 1 (η₁ / (2 * Real.sinh 2)) / 2 < θ := by linarith
    have hvol : ENNReal.ofReal vN ≤ volH (j + m) D := hCovN Λ hdisc D hD
    have hconv : min (cT / 2) cK * θ ^ (-1 : ℝ) ≤ vN := by
      have h1 : min (cT / 2) cK ≤ cK := min_le_right _ _
      have h2 : (0 : ℝ) ≤ θ ^ (-1 : ℝ) := (Real.rpow_pos_of_pos hθ0 _).le
      have h3 : cK * θ ^ (-1 : ℝ) ≤ vN := by
        have h4 : θ ^ (-1 : ℝ) ≤ (min 1 (η₁ / (2 * Real.sinh 2)) / 2) ^ (-1 : ℝ) := by
          rw [Real.rpow_neg_one, Real.rpow_neg_one]
          exact (inv_le_inv₀ hθ0 (by positivity)).mpr hthalf.le
        calc cK * θ ^ (-1 : ℝ)
            ≤ cK * (min 1 (η₁ / (2 * Real.sinh 2)) / 2) ^ (-1 : ℝ) :=
              mul_le_mul_of_nonneg_left h4 (le_of_lt hcKpos)
          _ = vN := by
              have hne : (min 1 (η₁ / (2 * Real.sinh 2)) / 2) ≠ 0 :=
                ne_of_gt (by positivity)
              rw [hcKdef, Real.rpow_neg_one, mul_assoc, mul_inv_cancel₀ hne, mul_one]
      calc min (cT / 2) cK * θ ^ (-1 : ℝ)
          ≤ cK * θ ^ (-1 : ℝ) := mul_le_mul_of_nonneg_right h1 h2
        _ ≤ vN := h3
    exact le_trans (ENNReal.ofReal_le_ofReal hconv) hvol

/-- **The master statement.**  Uniformly over all admissible splits of `n`, a fixed-free block
element whose `rotN` is at most `2 θ` and which is `rotN`-minimal in its centraliser kernel forces
the covolume to be at least `C * θ ^ (-A)`.

The proof takes the minimum of the per-split constants supplied by `Work.Mostow.thinStrataGood`
over the finite set of admissible splits. -/
theorem strataMaster (n : ℕ) (hn : 3 ≤ n) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (j m : ℕ) (e : j + m = n) (Λ : Subgroup (PO n 1)) (D : Set (E n))
        (R : E m ≃ₗᵢ[ℝ] E m) (θ : ℝ),
        2 ≤ j → 1 ≤ m → IsDiscrete (Λ : Set (PO n 1)) → IsFundamentalDomain Λ D (volH n) →
        (e ▸ blk j m 1 R : PO n 1) ∈ Λ → (∀ w : E m, R w = w → w = 0) → 0 < rotN R →
        rotN R ≤ 2 * θ → 0 < θ → θ ≤ 1 →
        (∀ c : PO n 1, c ∈ Λ → c ∈ Subgroup.centralizer {(e ▸ blk j m 1 R : PO n 1)} →
          resStd j m (e.symm ▸ c : PO (j + m) 1) = 1 → c ≠ 1 →
          rotN R ≤ rotN (nrmStd j m (e.symm ▸ c : PO (j + m) 1))) →
        ENNReal.ofReal (C * θ ^ (-A)) ≤ volH n D := by
  classical
  have hper : ∀ p ∈ tsg_splits n, ∃ x : ℝ × ℝ, 0 < x.1 ∧ 0 < x.2 ∧ TsgGood p x.1 x.2 := by
    intro p hp
    obtain ⟨-, h2, h3⟩ := (tsg_mem_splits.mp hp)
    obtain ⟨c, α, hc, ha, hg⟩ := tsg_goodInline p.1 p.2 h2 h3
    exact ⟨(c, α), hc, ha, hg⟩
  have hSne : (tsg_splits n).Nonempty := by
    refine ⟨(2, n - 2), ?_⟩
    rw [tsg_mem_splits]; omega
  let data : {p : ℕ × ℕ // p ∈ tsg_splits n} → ℝ × ℝ :=
    fun q => Classical.choose (hper q.1 q.2)
  have hdata : ∀ q : {p : ℕ × ℕ // p ∈ tsg_splits n},
      0 < (data q).1 ∧ 0 < (data q).2 ∧ TsgGood q.1 (data q).1 (data q).2 :=
    fun q => Classical.choose_spec (hper q.1 q.2)
  have hatt : (tsg_splits n).attach.Nonempty := ⟨⟨(2, n - 2), by rw [tsg_mem_splits]; omega⟩, by simp⟩
  have hIm : ((tsg_splits n).attach.image (fun q => (data q).1)).Nonempty :=
    hatt.image _
  have hIm2 : ((tsg_splits n).attach.image (fun q => (data q).2)).Nonempty :=
    hatt.image _
  let C : ℝ := ((tsg_splits n).attach.image (fun q => (data q).1)).min' hIm
  let A : ℝ := ((tsg_splits n).attach.image (fun q => (data q).2)).min' hIm2
  have hCpos : 0 < C := by
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp (Finset.min'_mem _ hIm)
    rw [show C = (data q).1 from hq.symm]; exact (hdata q).1
  have hApos : 0 < A := by
    obtain ⟨q, -, hq⟩ := Finset.mem_image.mp (Finset.min'_mem _ hIm2)
    rw [show A = (data q).2 from hq.symm]; exact (hdata q).2.1
  refine ⟨C, A, hCpos, hApos, ?_⟩
  intro j m e Λ D R θ hj hm hdisc hD hb hfree hRpos hR2θ hθ0 hθ1 hsep
  have hp : (j, m) ∈ tsg_splits n := by rw [tsg_mem_splits]; exact ⟨e, hj, hm⟩
  let q : {p : ℕ × ℕ // p ∈ tsg_splits n} := ⟨(j, m), hp⟩
  have hgood : TsgGood (j, m) (data q).1 (data q).2 := (hdata q).2.2
  have hCle : C ≤ (data q).1 :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q, by simp, rfl⟩)
  have hAle : A ≤ (data q).2 :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨q, by simp, rfl⟩)
  have hgood' := hgood (e.symm ▸ Λ : Subgroup (PO (j + m) 1)) (e.symm ▸ D : Set (E (j + m))) R θ
    (tsg_isDiscrete_cast e Λ hdisc) (tsg_isFundamentalDomain_cast e Λ D hD)
    (tsg_mem_cast e Λ (blk j m 1 R) hb) hfree hRpos hR2θ hθ0 hθ1 (tsg_sep_cast e Λ R hsep)
  have hrpow : θ ^ (-A) ≤ θ ^ (-(data q).2) :=
    Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1 (by linarith)
  have hmul : C * θ ^ (-A) ≤ (data q).1 * θ ^ (-(data q).2) :=
    mul_le_mul hCle hrpow (Real.rpow_nonneg hθ0.le _) (hdata q).1.le
  refine le_trans (ENNReal.ofReal_le_ofReal hmul) (le_trans hgood' (le_of_eq (tsg_volH_cast e.symm D)))

/-- The stratum adaptation lemma — the statement of `Work.Mostow.strataAdapt` (proved in
`Submission/Work/Mostow/strataAdapt.lean`) — taken as a parameter so that the assembly above could
be checked before it landed. -/
abbrev TsgAdapt : Prop :=
  ∀ (k m : ℕ), 2 ≤ k → 1 ≤ m →
    ∀ (Λ : Subgroup (PO (k + m) 1)) (D : Set (E (k + m))) (S : E m ≃ₗᵢ[ℝ] E m),
      IsDiscrete (Λ : Set (PO (k + m) 1)) → IsFundamentalDomain Λ D (volH (k + m)) →
      blk k m 1 S ∈ Λ → 0 < rotN S → (∃ w : E m, S w = w ∧ w ≠ 0) →
      (∀ c : PO (k + m) 1, c ∈ Λ → (∀ v : E k, c • coordEmb k m v = coordEmb k m v) → c ≠ 1 →
        rotN S ≤ rotN (nrmStd k m c)) →
      ∃ (j' m' : ℕ) (hj'm' : j' + m' = k + m) (Λ' : Subgroup (PO (k + m) 1))
        (D' : Set (E (k + m))) (R' : E m' ≃ₗᵢ[ℝ] E m'),
        2 ≤ j' ∧ 1 ≤ m' ∧
        IsDiscrete (Λ' : Set (PO (k + m) 1)) ∧
        IsFundamentalDomain Λ' D' (volH (k + m)) ∧
        volH (k + m) D' = volH (k + m) D ∧
        (hj'm' ▸ blk j' m' 1 R' : PO (k + m) 1) ∈ Λ' ∧
        (∀ w : E m', R' w = w → w = 0) ∧
        rotN R' ≤ rotN S ∧
        (∀ c' : PO (k + m) 1, c' ∈ Λ' →
          c' ∈ Subgroup.centralizer {(hj'm' ▸ blk j' m' 1 R' : PO (k + m) 1)} →
          resStd j' m' (hj'm'.symm ▸ c' : PO (j' + m') 1) = 1 → c' ≠ 1 →
          rotN R' ≤ rotN (nrmStd j' m' (hj'm'.symm ▸ c' : PO (j' + m') 1)))

/-- **The assembly.**  Given the stratum-adaptation lemma, the covolume gap at a stratum follows
from the master statement and the `rotN`-minimal element of the pointwise stabiliser. -/
theorem thinStrataGap_of_adapt (n : ℕ) (hn : 3 ≤ n) (hadapt : TsgAdapt) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
      ∀ (k m : ℕ) (hkm : k + m = n) (Λ : Subgroup (PO (k + m) 1)) (D : Set (E (k + m)))
        (R : E m ≃ₗᵢ[ℝ] E m), 2 ≤ k → 1 ≤ m →
        IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH (k + m)) →
        blk k m 1 R ∈ Λ → R ≠ LinearIsometryEquiv.refl ℝ (E m) →
        ∀ θ : ℝ, 0 < θ → θ ≤ 1 → NearIdAt (blk k m 1 R) (coordEmb k m 0) θ →
          ENNReal.ofReal (c * θ ^ (-α)) ≤ volH (k + m) D := by
  obtain ⟨C, A, hCpos, hApos, hMaster⟩ := strataMaster n hn
  refine ⟨C, A, hCpos, hApos, ?_⟩
  intro k m hkm Λ D R hk2 hm1 hdisc hD hb hRne θ hθ0 hθ1 hN
  subst hkm
  have hAk : POActionProp k := poAction_ge1 k (by omega)
  have hIk : HypIsometryProp k := hypIsometry_ge1 k (by omega) hAk
  have hA : POActionProp (k + m) := poAction_ge1 (k + m) (by omega)
  have hI : HypIsometryProp (k + m) := hypIsometry_ge1 (k + m) (by omega) hA
  -- the bridge: `NearIdAt` bounds `rotN`
  have hrot : rotN R ≤ 2 * θ := rotN_le_of_nearIdAt k m hAk hIk hA hI R 0 θ hθ1 hN
  have hRpos : 0 < rotN R := by
    have h : 0 ≤ rotN R := by rw [rotN]; exact norm_nonneg _
    rcases lt_or_eq_of_le h with h' | h'
    · exact h'
    · exact absurd (tsg_rotN_eq_zero R h'.symm) hRne
  -- the `rotN`-minimal element of the pointwise stabiliser of the stratum
  obtain ⟨R₀, hR₀pos, hR₀le, hb₀mem, hmin⟩ :=
    exists_min_pointwiseStab k m hk2 hA hI Λ hdisc R hb hRpos
  by_cases hfree : ∀ w : E m, R₀ w = w → w = 0
  · -- the good case: the fixed stratum of `blk k m 1 R₀` is the standard stratum
    have hFix : fixSet (blk k m 1 R₀) = stdTG k m :=
      fixSet_blk_eq_stdTG k m hAk hIk hA hI R₀ hfree
    have hcomm : ∀ c : PO (k + m) 1, c ∈ Subgroup.centralizer {blk k m 1 R₀} →
        blk k m 1 R₀ * c = c * blk k m 1 R₀ :=
      fun c hc => (Subgroup.mem_centralizer_iff.mp hc) (blk k m 1 R₀) (Set.mem_singleton _)
    have hsep0 : ∀ c : PO (k + m) 1, c ∈ Λ → c ∈ Subgroup.centralizer {blk k m 1 R₀} →
        resStd k m c = 1 → c ≠ 1 → rotN R₀ ≤ rotN (nrmStd k m c) := by
      intro c hcΛ hccen hrs hcne
      have hc := hcomm c hccen
      have hstab : c ∈ SetStabStd k m := by
        intro u
        rw [← hFix]
        constructor
        · intro hu
          show blk k m 1 R₀ • (c • u) = c • u
          rw [← (hA.2.2.2.2.1 (blk k m 1 R₀) c u), hc, (hA.2.2.2.2.1 c (blk k m 1 R₀) u), hu]
        · intro hu
          show blk k m 1 R₀ • u = u
          have h2 : c • (blk k m 1 R₀ • u) = c • u := by
            rw [← (hA.2.2.2.2.1 c (blk k m 1 R₀) u), ← hc,
              (hA.2.2.2.2.1 (blk k m 1 R₀) c u)]
            rw [hu]
          have h3 := congrArg (fun w => c⁻¹ • w) h2
          rwa [← (hA.2.2.2.2.1 c⁻¹ c (blk k m 1 R₀ • u)), inv_mul_cancel, hA.2.2.2.1,
            ← (hA.2.2.2.2.1 c⁻¹ c u), inv_mul_cancel, hA.2.2.2.1] at h3
      have hform : c = blk k m 1 (nrmStd k m c) := by
        conv_lhs => rw [rhd_stab_eq_blk k m hAk hIk hA hI c hstab]
        rw [hrs]
      have hcfix : ∀ v : E k, c • coordEmb k m v = coordEmb k m v := fun v => by
        rw [hform]
        exact blk_one_smul_coordEmb k m hAk hIk hA hI (nrmStd k m c) v
      exact hmin c hcΛ hcfix hcne
    have hsep : ∀ c : PO (k + m) 1, c ∈ Λ →
        c ∈ Subgroup.centralizer {((rfl : k + m = k + m) ▸ blk k m 1 R₀ : PO (k + m) 1)} →
        resStd k m ((rfl : k + m = k + m).symm ▸ c : PO (k + m) 1) = 1 → c ≠ 1 →
        rotN R₀ ≤ rotN (nrmStd k m ((rfl : k + m = k + m).symm ▸ c : PO (k + m) 1)) :=
      fun c h1 h2 h3 h4 => hsep0 c h1 (by simpa using h2) (by simpa using h3) h4
    exact hMaster k m (rfl : k + m = k + m) Λ D R₀ θ hk2 hm1 hdisc hD hb₀mem hfree hR₀pos
      (le_trans hR₀le hrot) hθ0 hθ1 hsep
  · -- the bad case: adapt the configuration to the fixed stratum of `blk k m 1 R₀`
    push_neg at hfree
    obtain ⟨w, hw, hwne⟩ := hfree
    obtain ⟨j', m', hj'm', Λ', D', R', hj'2, hm'1, hdisc', hD', hvol', hb', hfree', hrot', hsep'⟩ :=
      hadapt k m hk2 hm1 Λ D R₀ hdisc hD hb₀mem hR₀pos ⟨w, hw, hwne⟩ hmin
    have hle : rotN R' ≤ 2 * θ := le_trans hrot' (le_trans hR₀le hrot)
    have hR'pos : 0 < rotN R' := by
      have h : 0 ≤ rotN R' := by rw [rotN]; exact norm_nonneg _
      rcases lt_or_eq_of_le h with h' | h'
      · exact h'
      · exfalso
        have hR1 : R' = 1 := tsg_rotN_eq_zero R' h'.symm
        obtain ⟨i⟩ : Nonempty (Fin m') := ⟨⟨0, hm'1⟩⟩
        have hv : (EuclideanSpace.single i (1 : ℝ) : E m') ≠ 0 := by
          intro h0
          have h1 := congrArg (fun (v : E m') => v i) h0
          simpa using h1
        exact hv (hfree' _ (by rw [hR1]; rfl))
    have hmain := hMaster j' m' hj'm' Λ' D' R' θ hj'2 hm'1 hdisc' hD' hb' hfree' hR'pos hle
      hθ0 hθ1 hsep'
    rwa [hvol'] at hmain

theorem thinStrataGap (n : ℕ) (hn : 3 ≤ n)
    (hA : ∀ k, 2 ≤ k → POActionProp k) (hI : ∀ k, 2 ≤ k → HypIsometryProp k)
    (hCov : ∀ j, 2 ≤ j → j < n → CovolLB j) :
    ∃ c α : ℝ, 0 < c ∧ 0 < α ∧ ∀ (k m : ℕ) (hkm : k + m = n) (Λ : Subgroup (PO (k + m) 1))
      (D : Set (E (k + m))) (R : E m ≃ₗᵢ[ℝ] E m), 2 ≤ k → 1 ≤ m →
      IsDiscrete (SetLike.coe Λ) → IsFundamentalDomain Λ D (volH (k + m)) →
      blk k m 1 R ∈ Λ → R ≠ LinearIsometryEquiv.refl ℝ (E m) →
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 → NearIdAt (blk k m 1 R) (coordEmb k m 0) θ →
        ENNReal.ofReal (c * θ ^ (-α)) ≤ volH (k + m) D :=
  thinStrataGap_of_adapt n hn (fun k m hk hm => strataAdapt k m hk hm)

end Work.Mostow
