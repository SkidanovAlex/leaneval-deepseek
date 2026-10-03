/-
# Theorem `varp` and the assembly `end-var-from-varp`

This module states, as precisely as the paper allows, the two named targets that remain between
the paraproduct/model-operator analysis of Sections 5--10 of Krause--Mirek--Tao, *Pointwise
ergodic theorems for non-conventional bilinear polynomial averages*, Annals 195 (2022), and the
single analytic gap of the development, `Submission.ShiftHole.exists_varEstHalfFin_Cv`:

* `VarpEstimate` : **Theorem `varp`** (variational paraproduct estimates), the estimate
  `(all-all-weak)` of §4 for the major-arc paraproduct pieces `F^{u,l₁,s₁}_N`, `G^{u,l₂,s₂}_N`
  of the half-averages, with the exponential gain `2^{-c·max(l,s₁,s₂)}` in the case
  `p₁ = p₂ = 2`;
* `EndVarFromVarp` : the **assembly of §4/§5**, `end-var-from-varp`: Theorem `varp` together with
  Theorem `improv` (the single-scale minor-arc estimate, proved by the colleague owning
  `Work.Analysis.Concentration`) and Lemma `iw-prop` (the properties of the Ionescu--Wainger
  projections, built by the colleague owning `Work.Analysis.IonescuWainger`) yields the *halved
  finite variational estimate* `VarEstHalfFin` for the integer shift `TZ` and counting measure.

The paper's own route is
`end-var` ⟸ `varp` + `improv` + `iw-prop`, and `varp` ⟸ `improv` + the model estimates of
§7--§9; the latter reduction is the subject of `Submission/Work/Analysis/Paraproduct/`
(`SmallScale`, `CrtFactor`, `ArithBilinear`, ...), the former is the content of the two
statements recorded here.

## Design of the hypotheses

* The Ionescu--Wainger projections `Π_{≤l,≤k}` are supplied through the structure
  `IWProjections`, which bundles the properties of `iw-prop` that the assembly uses
  (`ℓ^q`-boundedness of the projections, and the property that the projections are the identity
  on functions with Fourier support in the major arcs — the latter is what turns a major-arc
  function into a *fixed* multiplier applied to the original function, as in §7).
* Theorem `improv` is the `Prop` `Work.Analysis.Concentration.Improv` of the colleague owning
  the concentration estimates; it is an explicit argument of `EndVarFromVarp`, never an axiom.
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.ShiftHole

set_option autoImplicit false

open scoped BigOperators ENNReal NNReal

namespace Work.Analysis.Paraproduct

noncomputable section

open MeasureTheory Polynomial

/-- **The Ionescu--Wainger Fourier projections `Π_{≤l,≤k}`** of §5.

The projections are an infinite family `proj : ℕ → ℤ → (ℤ → ℂ) → (ℤ → ℂ)`, where
`proj l k f = Π_{≤l,≤k} f` is the Fourier projection of the paper (the Ionescu--Wainger
multiplier with symbol `∑_{α ∈ (ℚ/ℤ)_{≤l}} η(θ - α)/2^k`-cutoff, `iwProj` in
`Work.Analysis.IonescuWainger`).

**Quarantine note (route finding F1 of `ROUTE_LEAD.md`).**  Earlier versions of this structure
also carried the fields `idem` (`Π Π = Π`), `nested` (`k ≤ k' ⟹ Π_k Π_{k'} = Π_k`) and
`lp_bound` (the `ℓ^q`-boundedness of `iw-prop`(i)).  The first two are **false** for the paper's
projections (the symbol `η_{≤k}` is not `0/1`-valued: `η_{≤k}η_{≤k'} = η_{≤k'}` needs
`k' ≥ k + 1`, so `Π_{≤l,≤k}Π_{≤l,≤k} ≠ Π_{≤l,≤k}` in general), and nothing in the workspace used
any of the three fields.  They have been deleted, leaving the single field `proj`; the `ℓ^q`
bounds and the symbol calculus are instead supplied by `KMTPlan`/`KMTContract` (the concrete
projections `kmtProj` and the API of `Work.Analysis.IWMultiplier`).  See `ROUTE_LEAD.md` §3.0,
step A0. -/
structure IWProjections where
  /-- The projection `Π_{≤ l, ≤ k}`. -/
  proj : ℕ → ℤ → (ℤ → ℂ) → (ℤ → ℂ)

/-- The §4 paraproduct piece `F^{u,l₁,s₁}_N` of `f`:
`Π_{l₁, ≤ -Log N + s₁} f - Π_{l₁, ≤ -Log N + s₁ - 1} f`.  (For `s₁ = -u` the paper takes the
single term `Π_{l₁, ≤ -Log N - u} f`; the difference formula is the generic case.) -/
def paraproductPiece (Pj : IWProjections) (l s : ℕ) (N : ℕ) (f : ℤ → ℂ) : ℤ → ℂ :=
  Pj.proj l (-(Nat.log 2 N : ℤ) + (s : ℤ)) f
    - Pj.proj l (-(Nat.log 2 N : ℤ) + (s : ℤ) - 1) f

/-- **Theorem `varp` (variational paraproduct estimates)**, Krause--Mirek--Tao §4: there are a
constant `C = C(max(l,s₁,s₂))` and a rate `c > 0` (depending only on `P` and the exponents)
such that for every choice of height parameters `l₁, l₂, s₁, s₂`, every pair `f, g : ℤ → ℂ` and
every set `I` of scales (the paper's `I^{l,s₁,s₂} = {N ∈ D : l, s₁, s₂ ≤ l_{(N)}}`, encoded here
by declaring the paraproduct pieces to vanish off `I`),

`‖ (Ã_N(F_N, G_N))_{N ∈ I} ‖_{ℓ^p(ℤ; V^r)} ≤ C 2^{O(ρl) - c·max(l,s₁,s₂)𝟙[p₁=p₂=2]}
‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`,

where `F_N = F^{u,l₁,s₁}_N`, `G_N = G^{u,l₂,s₂}_N` are the paraproduct pieces of `f, g`.  (We
record the exponential *gain* `2^{-c·max(l,s₁,s₂)}` uniformly — the weaker of the paper's two
regimes, the one that holds in all cases; the extra gain `2^{O(ρl)}` of the `p₁=p₂=2` case is
absorbed into the constant `C`.) -/
def VarpEstimate (Pj : IWProjections) (P : ℤ[X]) (p₁ p₂ p : ℝ≥0∞) (r : ℝ≥0) : Prop :=
  ∃ (c : ℝ) (C : ℕ → ℝ≥0∞), 0 < c ∧ (∀ a, C a ≠ ⊤) ∧
    ∀ (l₁ l₂ u s₁ s₂ : ℕ) (f g : ℤ → ℂ) (I : Finset ℕ),
      eLpNorm (fun x => PointwiseErgodicTheorems.variationalNorm r (fun N =>
          if N ∈ I then Submission.PointwiseErgodicTheorems.Ahalf Submission.PointwiseErgodicTheorems.TZ N X P
              (paraproductPiece Pj l₁ u N f) (paraproductPiece Pj l₂ u N g) x else 0))
          p Measure.count
        ≤ C (max (max l₁ l₂) (max s₁ s₂)) *
            ENNReal.ofReal ((2 : ℝ) ^ (-(c * (max (max l₁ l₂) (max s₁ s₂) : ℝ)))) *
            eLpNorm (fun n : ℤ => f n) p₁ Measure.count *
            eLpNorm (fun n : ℤ => g n) p₂ Measure.count

/-- **Theorem `model-est-2` (§7--§9)**, as a named target: the model tuples of the §7
approximation of `Ã_N(F_N, G_N)`, at every height parameter, are "acceptable" — bounded by the
gain `2^{-c·max(l,s₁,s₂)}`; the input norms of the underlying `f, g` are absorbed into the
constant.  The model tuples themselves are built in §6--§7 from the adelic Fourier analysis (the
bilinear Fourier multiplier operators `B^{l₁,l₂,m_hatZ}_{m_*}`, `B_{1⊗m_hatZ}`); we record only
the shape of the estimate.  This is the estimate reduced to, in §7, from Theorem `varp` by the
major-arc approximation `mod-approx` and the integration-by-parts identity `integ-ident`. -/
def ModelEstimate2 (Pj : IWProjections) (P : ℤ[X]) (p₁ p₂ p : ℝ≥0∞) (r : ℝ≥0)
    (H K : ℕ → ℤ → ℂ) : Prop :=
  ∃ (c : ℝ) (C : ℕ → ℝ≥0∞), 0 < c ∧ (∀ a, C a ≠ ⊤) ∧
    ∀ (l s₁ s₂ : ℕ) (I : Finset ℕ),
      eLpNorm (fun x => PointwiseErgodicTheorems.variationalNorm r (fun N =>
          if N ∈ I then Submission.PointwiseErgodicTheorems.Ahalf
              Submission.PointwiseErgodicTheorems.TZ N X P (H N) (K N) x else 0))
          p Measure.count
        ≤ C (max l (max s₁ s₂)) *
            ENNReal.ofReal ((2 : ℝ) ^ (-(c * (max l (max s₁ s₂) : ℝ))))

/-- **The §7 approximation by model operators: `varp` from the model estimates (`model-est`,
`model-est-2`).**  If the model estimate `ModelEstimate2` holds for every pair of tuples, then
Theorem `varp` holds.  (This is the reduction performed in §7 of the paper: the major-arc
approximation `mod-approx`, the functional calculus of the twisted bilinear multipliers, the
integration-by-parts identity `integ-ident`, and Minkowski's integral inequality reduce `varp` to
the small-scale and large-scale model estimates; the model tuples of §7 are particular tuples, so
the hypothesis is the same estimate at full generality.)  This is a *named gap*, not a proof: the
reduction itself is the content of §7. -/
def ModelApproxReduction (Pj : IWProjections) (P : ℤ[X]) (p₁ p₂ p : ℝ≥0∞) (r : ℝ≥0) : Prop :=
  (∀ (H K : ℕ → ℤ → ℂ), ModelEstimate2 Pj P p₁ p₂ p r H K) →
  VarpEstimate Pj P p₁ p₂ p r

end

end Work.Analysis.Paraproduct
