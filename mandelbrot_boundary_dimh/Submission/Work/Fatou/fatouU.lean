import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Setup
import Submission.Work.Fatou.FX8.Assembly
import Submission.Work.FatouCH.fatouEnds

/-! Guidance from the project lead (the requester):

AREA FATOU (uniformization route): prove `fatouU (hU : UniformizationHyp) : FatouStatement` (Interfaces/Fatou.lean). UniformizationHyp is the uniformization theorem, given to you as a HYPOTHESIS: use it for the existence of Phi (FX4-FX8) and nothing else from the uniformization library. A second FATOU route (Cauchy-Heine contraction) runs in parallel against the same contract; the first to land with clean axioms is kept.
Available sorry-free here: Submission.Unif.* (growth theorem Submission.exists_growth_bound_normalized_injective, Commons.Analysis.Complex.Landau.landau_theorem, Commons.Analysis.Complex.Koebe.weak_koebe_of_landau, Hurwitz), Submission.Work.Normal (Montel, hurwitz_nonvanishing).
Start in parallel: FX0-FX3, FX6 (QCLiouville), FX7 (InjEntireTranslation), FX9 (FatouDerivEstimate) - their Props are already in Interfaces/Fatou.lean; then FX4 -> FX5 -> FX8; then FX10-FX12.

## 1. The interface (what the FATOU area delivers) — `MandelDim.FatouStatement`

Definitions: `Qreg b₁ b₂` (Shishikura's 𝒬, `none` = ∓∞), `QAdm` (Re b₂ > Re b₁ + 4),
`NearTranslationOn F Q` (holomorphic, `‖F z − (z+1)‖ ≤ 1/32`, `‖F' z − 1‖ ≤ 1/32` — **1/32 instead of
the paper's 1/4**: costs nothing downstream, since F_f − (w+1) = O(1/dist(w, lattice)) and ξ₁, R₀ are
ours to enlarge, and it makes every fundamental-domain estimate slack), `IsFatouCoordOn F Φ Q`
(holomorphic, injective, `Φ (F z) = Φ z + 1` whenever `z, F z ∈ Q`).

`FatouStatement := FatouExists ∧ FatouOrbit ∧ FatouUnique ∧ FatouContinuity ∧ FatouDerivEstimate ∧ FatouEnds`
- `FatouExists`: Φ exists and `∀ w, ∃ z ∈ Q, ∃ n : ℤ, Φ z = w + n` (A.2.3: the cylinder is all of ℂ/ℤ ≅ ℂ*).
- `FatouOrbit`: `Φ z' = Φ z + k` (k : ℕ) ⇒ `F^[k] z = z'` with all intermediate iterates in Q.
- `FatouUnique`: any two Fatou coordinates on Q differ by a constant.
- `FatouContinuity`: moving domains `Qreg (b₁ n) (b₂ n)` whose every compact-of-the-limit is eventually
  inside, `F n → F₀` uniformly on compacts, normalization at one point ⇒ `Φ n → Φ₀` uniformly on compacts
  (this is exactly A.2.1(iii) in the form (4.2.4) needs: 𝒬_f^+ = 𝒬(ξ₁, −ξ₁+1/α) → 𝒬(ξ₁, ∞)).
- `FatouDerivEstimate`: Lemma A.2.4(i), universal R₁ C₁ C₂.
- `FatouEnds`: if `‖F z − (z+ρ)‖ ≤ M e^{−κ Im z}` high up (resp. low down) in Q, then
  `Φ z = z/ρ + c + o(1)` there, uniformly on vertical strips of width 4. This replaces the paper's use of
  A.2.4(ii)/(A.4.1)–(A.4.3) for the extension of E_f, R_f to 0 and ∞ and for R_f'(0) = e^{−2πi/α}:
  e.g. at the upper end ρ = 1 for both Φ_{±,f}, so R̃_f = Φ_−∘T_f∘Φ_−⁻¹ = w − 1/α + o(1).
  (Perturbed F_f: at the upper end F_f → w+1 exponentially in Im(αw) ≥ (Re α − |Im α|) Im w − 1; at the
  lower end F_f → w + ρ with ρ = −log f'(σ)/(2πiα), |ρ − 1| = O(α) — NOT ρ = 1, which is why ρ is free.)
- Optional, not in the contract: `FatouSectorAsymptotic` (A.2.4(ii)); proof in §5. The unperturbed
  asymptotics φ₀* = w + a log w + b + o(1) (4.1.2) come from the FatouCoord library (PARAB0), not from here.

## 2. Construction, lemma by lemma (build order FX0 → FX12)

Notation: Q = Qreg b₁ b₂ admissible, ε(z) := F z − z − 1, |ε|, |ε'| ≤ 1/32 on Q. Fix
x₀ := Re b₁ + 3/2 if b₁ = some, else (Re b₂ − 5/2 if b₂ = some, else 0). Then the vertical strip
{x₀ − 1 − 1/4 < Re < x₀ + 2 + 1/4} ⊂ Q (Q ⊇ {Re b₁ < Re < Re b₂}).

**FX0 geometry (1–1.5K).** `isOpen_Qreg`; Q ⊇ the vertical strip {Re b₁ < Re < Re b₂}; one step of F
changes Re by [31/32, 33/32] and Im by ≤ 1/32; the quantity Re(z−b₁)+|Im(z−b₁)| increases and
|Im(z−b₂)| − Re(z−b₂) increases under F (resp. F⁻¹), so forward orbits never leave through the left
cone and backward orbits never through the right one. **Inverse:** if the closed disc B̄(z−1, 1/16) ⊂ Q
then w ↦ z − 1 − ε(w) is a 1/32-contraction of that disc into itself ⇒ unique w with F w = z (Banach
fixed point, `ContractingWith`). F⁻¹ is holomorphic where defined (`HasDerivAt.of_local_left_inverse`,
F' ≠ 0).

**FX1 = A.2.1(0) `FatouInjOnQ` (0.5–1K).** Suppose F z₁ = F z₂, z₁ ≠ z₂; then d := |z₁−z₂| ≤ 1/16.
The complement of Q near b₁ is the convex cone K₁ = {Re u + Im u ≤ 0} ∩ {Re u − Im u ≤ 0} (u = z−b₁), so
ℂ∖K₁ = P₁ ∪ P₂ with P₁ = {Re u + Im u > 0}, P₂ = {Re u − Im u > 0} open half-planes. If z₁, z₂ lie in a
common Pᵢ the segment is in Q; otherwise (one in P₁∖P₂, other in P₂∖P₁) go through p := b₁ + d (∈ P₁∩P₂):
path length ≤ (2+2√2)d. Same at b₂ (the two cones are > 2 apart, a path of length < 1/2 meets at most
one). Then |F z₁ − F z₂ − (z₁ − z₂)| ≤ (1/32)(2+2√2)d < d, contradiction.

**FX2 = A.2.1(i) `FatouFundamental` (1–1.5K).** `fundStrip F Q x₀ = {z ∈ Q | x₀ ≤ Re z ∧ every
F-preimage in Q has Re < x₀}` (= S ∖ F(ℓ), no graph of F(ℓ) needed). Existence: Re z < x₀ ⇒ iterate
forward (stays in Q by FX0; the vertical strip covers Re < x₀+2) until first Re ≥ x₀; Re z ≥ x₀ ⇒ iterate
F⁻¹ (FX0 disc condition holds because Re > x₀ − 1/8 keeps B̄(z−1,1/16) inside the strip) until first
Re < x₀ and take the next point. Uniqueness: if s and F^k s (k ≥ 1) are both in fundStrip, the preimage
F^{k−1} s of F^k s has Re ≥ Re s + (k−1)·31/32 ≥ x₀, contradiction.

**FX3 the interpolation devH (1–2K).** χ : ℝ → ℝ the C¹ smoothstep: 0 on (−∞,1/8], 1 on [7/8,∞),
s((t−1/8)/(3/4)) between, s(u) = 3u² − 2u³; |χ'| ≤ 2. (Mathlib's `Real.smoothTransition` has no explicit
derivative bound; use the smoothstep and prove C¹ by hand, ~200 lines.)
`devH ζ := x₀ + ζ + χ(Re ζ) · ε(x₀ + ζ − 1)` on Σ := {−1/8 < Re ζ < 9/8}. Facts:
(a) `devH ζ = x₀ + ζ` for Re ζ ≤ 1/8; `devH ζ = F(x₀ + ζ − 1)` for Re ζ ≥ 7/8;
(b) **equivariance** `devH (ζ+1) = F (devH ζ)` for |Re ζ| < 1/8 (from (a));
(c) Wirtinger: ∂(χε) = χε' + (χ'/2)ε, ∂̄(χε) = (χ'/2)ε ⇒ |∂ devH − 1| ≤ 1/16, |∂̄ devH| ≤ 1/32, so
‖D devH − I‖ ≤ 3/32: devH is injective on the convex Σ with |devH ζ₁ − devH ζ₂| ≥ (29/32)|ζ₁−ζ₂|, open
(IFT: `HasStrictFDerivAt.map_nhds_eq`), C¹, dilatation |∂̄/∂| ≤ 1/30;
(d) devH(Σ) ⊂ Q and devH(Σ) ⊇ {x₀ − 3/32 < Re < x₀ + 1 + 3/32} (Banach fixed point for
ζ = s − x₀ − χ(Re ζ)ε(x₀+ζ−1) on B̄(s−x₀, 1/32));
(e) **STRIP**: devH maps {0 ≤ Re ζ < 1} bijectively onto fundStrip. Into: three cases Re ζ ∈ [0,1/8],
(1/8,7/8), [7/8,1) using (a) and the Re-step bounds (all slack ≥ 1/16). Onto: by (d) s = devH ζ with
ζ ∈ Σ; Re ζ < 0 ⇒ Re s < x₀; Re ζ ≥ 1 ⇒ s = F(x₀+ζ−1) has a preimage with Re ≥ x₀; both contradict.

**FX4 the Riemann surface (3–5K; plumbing).** Bundle `structure FatouData` (b₁ b₂ F + proofs of QAdm,
NearTranslationOn), `def XF (D : FatouData) : Type := ℂ` (a `def`, so ℂ's own ChartedSpace instance is
NOT visible), `instance : TopologicalSpace (XF D) := inferInstanceAs _` (same for T2, connected,
second countable, `SimplyConnectedSpace`). Charts `chart n : OpenPartialHomeomorph (XF D) ℂ` via
`OpenPartialHomeomorph.ofContinuousOpen` (checked: takes a `PartialEquiv`, `ContinuousOn`, `IsOpenMap`,
`IsOpen source`), source {n−1/8 < Re < n+9/8}, map ζ ↦ devH(ζ−n), inverse `Function.invFunOn` + n.
`chartAt ζ := chart ⌊Re ζ⌋`, atlas = range chart. Transitions (FX3(b)): chart (n+1) ∘ (chart n)⁻¹ = F⁻¹ on
F(x₀ + {|Re| < 1/8}), its inverse is F; charts n, m with |n−m| ≥ 2 have disjoint sources (width 5/4 < 2).
`IsManifold (modelWithCornersSelf ℂ ℂ) 1 (XF D)` via `isManifold_of_contDiffOn` (ContDiffOn ℂ 1 of
id / F / F⁻¹). Deck map `T ζ := ζ + 1` is ContMDiff (in charts: identity from n to n+1) and bijective ⇒
`Diffeomorph`. Noncompactness: `¬ CompactSpace ℂ`.

**FX5 uniformize (0.3K).** Wrapper theorem (copy of the 6-line proof in the uniformization lib's root
`Submission.lean`): `Work.Drive.uniformization_of_parts hX x (Work.Drive.periodsHold_of_subsingleton_hom hX x)
(fun hP hW => Work.Drive.weak_case hX x hP hW) (fun hP hO => Work.Drive.liouville_case hX x hP hO)`,
conclusion `Work.Drive.Conclusion X = Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ ℂ) ∨ Nonempty (X ≃ₘ⟮mℂ, mℂ⟯ UpperHalfPlane)`.
Put it in our own module (the lib's `Submission.lean` root cannot be copied).

**FX6 exclude ℍ: `QCLiouville` (2–4K).** Statement in the .txt (g : ℂ → ℂ C¹, injective, ∂g ≠ 0,
|∂̄g| ≤ k|∂g|, k < 1, |g| ≤ M ⇒ False). Proof: J := |∂g|² − |∂̄g|² = det Dg ≥ 0 and
‖Dg‖ = |∂g| + |∂̄g| ⇒ ‖Dg‖² ≤ K·J with K = (1+k)/(1−k) (equality K(1−k²) = (1+k)²). g is an open map (IFT,
J > 0), so for r ≥ 1 the boundary of the compact g(D̄_r) lies in g(∂D_r); for compact K ⊂ ℂ,
diam ∂K ≥ diam K (extend the chord xy to the last points of K on that line); hence
diam g(∂D_r) ≥ d := |g 1 − g(−1)| > 0. Arc ≥ chord (FTC along θ ↦ g(re^{iθ})):
d ≤ ∫₀^{2π} ‖Dg(re^{iθ})‖ r dθ; Cauchy–Schwarz: d²/(2πr) ≤ ∫₀^{2π} ‖Dg‖² r dθ ≤ K ∫₀^{2π} J r dθ.
Integrate r ∈ [1,R], polar coordinates (`integral_comp_polarCoord_symm`), area formula
(`MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image`, injective): (d²/2π) log R ≤ K·area g(annulus)
≤ KπM². R → ∞: contradiction.
Application: Ψ : XF ≃ₘ ℍ, g := cayley ∘ Ψ (cayley τ = (τ−i)/(τ+i), |g| < 1). On each chart source
g = Gₙ ∘ devH(· − n) with Gₙ := cayley ∘ Ψ ∘ (chart n)⁻¹ holomorphic and injective, so Gₙ' ≠ 0
(`Commons.Analysis.Complex.deriv_ne_zero_of_injective_analytic` in the lib, or Mathlib's
injective-analytic lemma); ∂g = Gₙ'·∂devH ≠ 0, |∂̄g|/|∂g| = |∂̄devH|/|∂devH| ≤ 1/30; g is C¹ on each open
chart source hence on ℂ. Contradiction ⇒ only the ℂ case remains.

**FX7 `InjEntireTranslation` (1.5–3K).** A entire, injective, no fixed point ⇒ A w = w + b, b ≠ 0.
A(ball 0 1) is open (open mapping) ⊇ ball(A 0, ρ); injectivity ⇒ |A z − A 0| ≥ ρ for |z| ≥ 1;
h(w) := 1/(A(1/w) − A 0) is bounded on 0<|w|<1 ⇒ removable (`differentiableOn_update_limUnder_of_bddAbove`,
checked). If h(0) ≠ 0, A is bounded ⇒ constant (Liouville), contradiction. Else h(w) = w^m u(w), u(0) ≠ 0
⇒ |A z| ≤ C|z|^m for |z| ≥ 2 ⇒ Cauchy estimates kill all Taylor coefficients of order > m ⇒ A polynomial;
an injective polynomial has degree 1 (a root of A' would contradict local injectivity); A w = aw + b, and
no fixed point ⇒ a = 1, b ≠ 0.

**FX8 assemble `FatouExists` + `FatouOrbit` (3–4K).** Ψ : XF ≃ₘ ℂ; A := Ψ ∘ T ∘ Ψ⁻¹ is entire, injective,
fixed-point-free ⇒ Ψ(ζ+1) = Ψ ζ + b (FX7). Π : Q → XF: z's unique orbit point s ∈ fundStrip (FX2), s =
devH ζ with 0 ≤ Re ζ < 1 (FX3e); Π z := ζ − k if F^k z = s, ζ + k if z = F^k s. Then Π(F z) = Π z + 1.
**REP lemma**: if w ∈ Q ∩ devH(Σ), w = devH ζ, then Π w = ζ (three cases Re ζ < 0 / ∈ [0,1) / ≥ 1, using
FX3(a),(b),(e)). Φ := Ψ ∘ Π / b. Holomorphic: near z pick m with F^m z ∈ fundStrip ⊂ devH(Σ) (open); by
REP, near z Φ = (Ψ ∘ (chart (−m))⁻¹)(F^m ·)/b (use F⁻¹ holomorphic for m < 0). Injective: Ψ and Π are
injective (Π z₁ = Π z₂ ⇒ same s and same level ⇒ z₁ = z₂). Abel: from Π(F z) = Π z + 1. Surjective mod ℤ:
b·w = Ψ ζ, n := ⌊Re ζ⌋, s := devH(ζ − n) ∈ fundStrip, Φ s = Ψ(ζ − n)/b = w − n. `FatouOrbit`: canonical
representatives + Ψ injective (both directions of the orbit stay in Q by FX2).

**FX9 `FatouDerivEstimate` = A.2.4(i) (2–3K).** Paper's proof, with the lib's weak Koebe instead of sharp
Koebe. (1) Koebe bounds: Φ univalent on B(z,2), |v(z) − 1| < 1/4, Φ(z+v) = Φ z + 1 ⇒ c ≤ |Φ'(z)| ≤ C
universal. Upper: `weak_koebe_of_landau` (with `landau_theorem`, c₀ = 1/100) ⇒ Φ(B(z,3/4)) ⊇
B(Φ z, (3/4)(c₀/π)|Φ'(z)|); if that radius exceeds 1 it contains Φ z + 1 = Φ(z+v), so by injectivity
|v| < 3/4, contradiction ⇒ |Φ'| ≤ 4π/(3c₀). Lower: `growth_bound` (hkoebe := weak_koebe_of_landau …)
applied to u ↦ (Φ(z+2u) − Φ z)/(2Φ'(z)) at u = v/2 (|u| ≤ 5/8) ⇒ 1/(2|Φ'(z)|) ≤ (13/3)^{π/c₀} − 1.
(2) With z₀ = 0, R ≥ R₁: |Φ'| ≤ C on B(0,R−2) ⇒ Cauchy |Φ''| ≤ C/R on B(0,R/2). Taylor
Φ(z+v) = Φ z + vΦ'(z) + v²∫₀¹(1−t)Φ''(z+tv)dt ⇒ |1 − Φ'(z)v(z)| ≤ C/R on B(0, R/2 − 5/4).
(3) Cauchy on that disc: |(1 − Φ'v)'| = |Φ''v + Φ'v'| ≤ C/R² on B(0,R/4); |v''| ≤ C/R² (|v−1| < 1/4 on
B(0,R)); so |v'(z)| ≤ |v'(0)| + C/R² for |z| ≤ 2 and |Φ''| ≤ C(1/R² + |v'(0)|) on B(0,2).
(4) Taylor at 0 again: |1 − Φ'(0)v(0)| ≤ C(1/R² + |v'(0)|), divide by |v(0)| ≥ 3/4 ⇒ C₁ bound; Cauchy
|v'(0)| ≤ 1/(4R) ⇒ C₂/R.

**FX10 `FatouUnique` (1–2K).** Φ₁ := the constructed one (surjective mod ℤ), Φ₂ arbitrary. D : ℂ → ℂ,
D w := Φ₂ z − Φ₁ z for any z ∈ Q, n ∈ ℤ with Φ₁ z = w + n; well defined by FatouOrbit; 1-periodic;
holomorphic (locally (Φ₂ − Φ₁)∘Φ₁⁻¹(· + n)). D'(w) = Φ₂'(z)/Φ₁'(z) − 1 with z the fundStrip
representative; as |Im w| → ∞ the representative's |Im z| → ∞ (Φ₁ is bounded on the compact closure of
fundStrip ∩ {|Im| ≤ Y}), and B(z, R) ⊂ Q with R ~ |Im z|/√2 → ∞, so by FX9 for both Φᵢ with v = F − id:
Φ₂'/Φ₁' → 1. So D' is entire, periodic, bounded ⇒ constant (Liouville) = its limit 0 ⇒ D constant.
Finally Φ arbitrary vs Φ₁ gives uniqueness for any pair.

**FX11 `FatouContinuity` (2–3K).** (a) Local uniform bounds of Φₙ on compacts of Q∞: pick z* ∈ Q∞ with
B(z*, 2R₁) ⊂ Q∞ (Q∞ has arbitrarily large discs high up); by FX9 |Φₙ'(z*)| ∈ [1/2, 2] eventually;
Koebe distortion (weak form, from growth_bound + Cauchy) propagates bounds on |Φₙ'| along a finite chain of
discs to any compact K (Q∞ open connected); with Φₙ(z₀) = Φ₀(z₀) integrate along paths ⇒ |Φₙ| ≤ C(K).
(b) Montel: `Work.Normal.montel_locallyBounded` (seed, sorry-free). (c) Any sub-limit Φ∞ satisfies the
Abel equation of F₀ (uniform convergence + equicontinuity), is injective (Hurwitz, `Work.Normal.
hurwitz_nonvanishing` applied to Φₙ − Φₙ(a) on Q∞∖{a}) and nonconstant (Abel). (d) FatouUnique on Q∞ +
normalization ⇒ Φ∞ = Φ₀. (e) Every subsequence has a sub-subsequence → Φ₀ ⇒ uniform convergence on K.

**FX12 `FatouEnds` (2–3K).** Upper end (lower: same, or conjugate everything by z ↦ z̄). Write
ψ := Φ⁻¹ on Φ(Q) and Ĝ(w) := P(ψ w) with P(z) := Φ z − z/ρ. (1) Φ'(z) → 1/ρ high up (FX9 with
v = F − id → ρ and R → ∞) ⇒ Ĝ' → 0 as Im w → ∞. (2) Ĝ(w+1) − Ĝ(w) = 1 − (F(ψ w) − ψ w)/ρ =: e(w),
|e(w)| ≤ M' e^{−κ' Im w}. (3) a(y) := ∫₀¹ Ĝ(t + iy) dt: by Cauchy on the rectangle [0,1]×[y₁,y₂]
(`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) a(y₂) − a(y₁) = i∫_{y₁}^{y₂} e(is) ds, integrable
⇒ a(y) → c. (4) |Ĝ(t+iy) − a(y)| ≤ sup|Ĝ'| → 0. Hence Ĝ → c uniformly on Re w ∈ [0,1], and on
Re ∈ [−3,4] by ≤ 4 unit shifts with defect e. Translate back: z high in a vertical strip ⇒ w = Φ z high up
(Φ is bounded on compacts) ⇒ Φ z − z/ρ = Ĝ(w) → c. Needs: Φ(Q) contains the unit-width horizontal
segments high up (surjectivity mod ℤ + FatouUnique to transfer from the constructed Φ₁).

## 6. What is NOT needed
- MRMT / Ahlfors–Bers / QC maps / Beurling L^p, the NN Beltrami solver, the Mori/λ-lemma.
- Any smoothness of devH for the complex structure (only C¹ for FX6).
- The paper's A.2.4(ii) and the constants c_± of (A.4.1): FatouEnds gives the end behaviour directly.
- Continuity in the "functions with domains" topology in general: only the sequence form above.
- Unperturbed coordinates on half-planes: already in `Submission/Work/FatouCoord` (seed); FatouUnique links
  them to the abstract ones on 𝒬(ξ₁, ∞) / 𝒬(−∞, −ξ₁).
-/

namespace Work.Fatou

open MandelDim

theorem fatouU (hU : UniformizationHyp) : FatouStatement := by
  exact FX8.fatouStatement_of hU
    (Work.FatouCH.fatouEnds (FX8.fatouExists hU) (FX8.fatouUnique hU)
      Work.Fatou.Analysis.fatouDerivEstimate)

end Work.Fatou
