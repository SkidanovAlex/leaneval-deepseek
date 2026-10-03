import Mathlib
import Submission.Work.Peluse.Holds.SwapDefs

/-!
# `SwapE` — the dense endgame of the regime-swap route (vocabulary)

This module is the vocabulary layer of the `SwapE` chapter, the owner of the node
`denseEndgame` (`Submission/Work/Peluse/P2P3_LEAD.md`, §3.6, node **END**).

The chapter is organised around the paper's *linear-in-law* mechanism
(Kravitz–Kuca–Leng, *Quantitative concatenation for polynomial box norms*, arXiv:2407.08636,
§7–§8, and in particular Corollary 7.2 and the passage from (57) to the end of the proof of
Theorem 1.10):

* the multiset slot `q₁[M] − q₂[M]` is a probability law `slotLaw q₁ q₂ M` on `ℤ`, whose
  **density** is controlled by the two-line solution count of KKL Corollary 7.2
  (at `ℓ = 2`): `slotLaw q₁ q₂ M n ≤ K₀/(4HM+1)` for a *generic* pair `(q₁,q₂)`
  (`genPair H η`), with `K₀ = endgameK0 η H M ≤ 32(1+H/M)/η²`;
* writing the box sum for `pbox` as a sum over the slot value `n ∈ ℤ^d`, with the *cube mass*
  `boxMass d S f n` (the `2^d`-fold cube sum along the directions `n`), turns `pbox` into a
  **linear functional of the joint law** of the slot values (`LinearInLaw`);
* since the uniform distribution on `[−2HM, 2HM]^d` dominates that joint law up to
  `(K₀)^d`, the hypothesis `δ ≤ pbox` gives `(δ/2)/K₀^d ≤ massAvg` (`SlotMassLower`);
* and the average of the cube mass over the slot box controls a Gowers uniformity norm at any
  window `[D]` with `D ≤ HM` (`UniformFromMass`).

`DenseEndgame` is the node statement; `Work.Peluse.SwapE.denseEndgame_of_pieces` reduces it to
the three Props above.  Namespace `Work.Peluse.SwapE`; the frozen vocabulary (`pbox`,
`pboxSum`, `pdir`, `avg`, `genPair`) is that of `Work.Peluse.LadderP.Swap`
(`Submission/Work/Peluse/Holds/SwapDefs.lean`), which this module only `open`s.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

/-! ## 0. The density constant and the slot law -/

/-- The endgame density constant `K₀ = 24/η² + 8H/M`.  It exceeds every constant the two-line
count of KKL Corollary 7.2 produces, and it satisfies `K₀ ≤ 32 (1 + H/M)/η²` for `0 < η ≤ 1`,
which is the only bound the assembly uses. -/
def endgameK0 (η : ℝ) (H M : ℕ) : ℝ := 24 / η ^ 2 + 8 * (H : ℝ) / (M : ℝ)

/-- The number of pairs of slot points `(m, m') ∈ [1,M]² × [1,M]²` whose slot difference
`pdir q₁ q₂ m − pdir q₁ q₂ m'` equals `n`.  This is `M⁴` times the law of the multiset slot
`q₁[M] − q₂[M]`. -/
def slotCount (q₁ q₂ : ℤ) (M : ℕ) (n : ℤ) : ℕ :=
  (((Finset.univ : Finset (Fin M × Fin M)) ×ˢ
      (Finset.univ : Finset (Fin M × Fin M))).filter
    (fun p => pdir q₁ q₂ p.1 - pdir q₁ q₂ p.2 = n)).card

/-- The law of the multiset slot `q₁[M] − q₂[M]`: the probability that the slot difference
`pdir q₁ q₂ m − pdir q₁ q₂ m'` of two independent uniform slot points equals `n`. -/
def slotLaw (q₁ q₂ : ℤ) (M : ℕ) (n : ℤ) : ℝ :=
  (slotCount q₁ q₂ M n : ℝ) / (M : ℝ) ^ 4

/-! ## 1. The cube mass of a slot value -/

/-- The cube mass of the slot value `n ∈ ℤ^d`:

`boxMass d S f n = |S|⁻¹ ∑_x ∏_{ω : Fin d → Bool} C^{|ω|} f (x + ω·n)`,

i.e. the `2^d`-fold cube term of `f` along the (singleton) directions `n_k`.  It is the
function of `n` whose average over the slot box is the endgame's `massAvg`. -/
def boxMass (d : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) (n : Fin d → ℤ) : ℂ :=
  ((S.card : ℂ))⁻¹ * ∑' x : ℤ, ∏ ω : Fin d → Bool,
    (star^[weight ω]) (f (x + cornerShift n (0 : Fin d → ℤ) ω))

/-- The half-width `2HM` of the slot box. -/
def massHalf (H M : ℕ) : ℤ := 2 * ((H * M : ℕ) : ℤ)

/-- The slot box `[−2HM, 2HM]^d`.  Every slot difference of the endgame lies in it, because the
slot coefficients are bounded by `H` and the differences of slot points by `M`. -/
def massBox (d H M : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(massHalf H M)) (massHalf H M))

/-- `4HM+1`, the size of one factor of the slot box: `#([−2HM,2HM])`. -/
def massBoxCard (H M : ℕ) : ℕ := 4 * H * M + 1

/-- The average of `‖boxMass‖` over the slot box.  This is the quantity which the endgame's
density argument produces, and which the uniformity-norm step consumes. -/
def massAvg (d H M N : ℕ) (f : ℤ → ℂ) : ℝ :=
  (∑ n ∈ massBox d H M, ‖boxMass d (symIcc N) f n‖) / ((massBoxCard H M : ℝ) ^ d)

/-! ## 2. The linear-in-law form of the box sum -/

/-- The linear-in-law sum: `∑_{n ∈ [±L]^d} (∏_k slotLaw (q₁ k) (q₂ k) M (n k)) · boxMass d S f n`.
It is the expansion of `pboxSum d q₁ q₂ M S f` over the *slot values*. -/
def lawSum (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) (L : ℕ) : ℂ :=
  ∑ n ∈ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) L),
    (∏ k : Fin d, (slotLaw (q₁ k) (q₂ k) M (n k) : ℂ)) * boxMass d S f n

/-! ## 3. The three pieces of the endgame -/

/-- **Piece 1 — the linear-in-law identity.**  The box sum along the multiset slots
`q₁ k[M] − q₂ k[M]` is the sum over the slot values `n ∈ ℤ^d` of the product of the slot laws
times the cube mass, truncated at any box `[±L]^d` containing the support of the cube mass
(`2N ≤ L`, since `f` is supported in `symIcc N`).

Proof: write the box sum over the slot points `(h, h')`, substitute `y = x + Σ_k pdir(h' k)`
in the (translation invariant) sum over `x`, observe that the summand depends on `(h,h')` only
through the slot differences `n_k = pdir(h k) − pdir(h' k)`, and count the fibre of that map
(`Finset.sum_fiberwise`). -/
def LinearInLaw : Prop :=
  ∀ (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M N L : ℕ) (S : Finset ℤ) (f : ℤ → ℂ),
    1 ≤ M → SupportIn f N → 2 * N ≤ L →
    pboxSum d q₁ q₂ M S f = lawSum d q₁ q₂ M S f L

/-- **Piece 2 — the slot density** (KKL Corollary 7.2 at `ℓ = 2`).  For a *generic* pair of slot
coefficients (`genPair H η`: both at least `ηH` in modulus and of gcd at most `1/η`), the law of
the slot difference is bounded by `K₀/(4HM+1)` — i.e. by the density of the uniform
distribution on the slot box `[−2HM,2HM]`, up to the constant `K₀ = endgameK0 η H M`.

Proof: `slotLaw` is a count of pairs `(X, Y) ∈ [±M]²` with `q₁X − q₂Y = n`, weighted by
`(M−|X|)(M−|Y|) ≤ M²`.  On the lattice coset `{aX − bY = n/g}` (`g = gcd(q₁,q₂)`,
`a = q₁/g`, `b = q₂/g`) the solutions are `(X₀ + bt, Y₀ + at)`, and `|X₀+bt|,|Y₀+at| ≤ M`
forces `|t| ≤ 2M/max(|a|,|b|) ≤ 2M/(η²H)`. -/
def SlotDensity : Prop :=
  ∀ (q₁ q₂ : ℤ) (M H : ℕ) (η : ℝ) (n : ℤ),
    1 ≤ M → 1 ≤ H → 0 < η → η ≤ 1 → genPair H η q₁ q₂ →
    slotLaw q₁ q₂ M n ≤ endgameK0 η H M / (4 * (H : ℝ) * (M : ℝ) + 1)

/-- **Auxiliary piece — the box sum is bounded by one.**  For `f` supported in `symIcc N` with
`‖f‖ ≤ 1` and `1 ≤ M`, the value of `pbox` is at most `1` (the integrand of `pboxSum` is
supported in `symIcc N` and bounded by `1`, and the double slot average has `M⁴` terms per slot).
This is what makes the "bad slots contribute at most `δ/2`" step work. -/
def PboxLeOne : Prop :=
  ∀ (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M N : ℕ) (f : ℤ → ℂ),
    1 ≤ M → SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
    pbox d q₁ q₂ M (symIcc N) f ≤ 1

open Classical in
/-- **Piece 3a — the slot-mass lower bound.**  From the endgame's hypotheses (`δ ≤ avg pbox`,
the bad slots are at most a `δ/2` proportion, the good slots have generic coefficients, and the
coefficients are bounded by `H`) one gets

`C δ / K₀^d ≤ massAvg d H M N f`.

Proof: at least one good slot `ω` has `pbox ω ≥ δ/2` (the bad ones contribute at most `δ/2`
because `pbox ≤ 1`); `LinearInLaw` writes `pbox ω = ∑_n (∏_k slotLaw) boxMass n`; every slot
value lies in the slot box, so the sum may be restricted to it; and `SlotDensity` bounds each
product of slot laws by `K₀^d/#(box)`. -/
def SlotMassLower : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (q₁ q₂ : Ω → Fin d → ℤ) (G : Finset Ω)
      (H M N : ℕ) (η δ : ℝ) (f : ℤ → ℂ),
      1 ≤ H → 1 ≤ M → 0 < η → η ≤ 1 → 0 < δ → SupportIn f N →
      (∀ x : ℤ, ‖f x‖ ≤ 1) →
      (∀ ω k, |q₁ ω k| ≤ (H : ℤ) ∧ |q₂ ω k| ≤ (H : ℤ)) →
      (∀ ω ∈ G, ∀ k, genPair H η (q₁ ω k) (q₂ ω k)) →
      (((Finset.univ \ G).card : ℝ) ≤ δ / 2 * (Fintype.card Ω : ℝ)) →
      δ ≤ avg (fun ω : Ω => pbox d (q₁ ω) (q₂ ω) M (symIcc N) f) →
      C * δ / (endgameK0 η H M) ^ d ≤ massAvg d H M N f

/-- **Auxiliary piece — the cube mass is bounded by one.**  For `f` supported in `symIcc N` with
`‖f‖ ≤ 1`, the cube mass `boxMass d (symIcc N) f n` is bounded by `1` (its integrand is supported
in `symIcc N` and bounded by `1`, and the normalising set has `2N+1` elements), so the average
`massAvg` over the slot box is at most `1`.  This is what makes the threshold `C δ/K₀^d` of
`SlotMassLower` an admissible argument for `UniformFromMass` (`θ ≤ 1`). -/
def MassAvgLeOne : Prop :=
  ∀ (d H M N : ℕ) (f : ℤ → ℂ),
    SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) → massAvg d H M N f ≤ 1

/-- **Piece 3b-i — the cube-mass average controls the box norm at the slot window** (KKL §8,
after (57)): Cauchy–Schwarz removes the modulus of the cube mass (`(E‖X‖)² ≤ E‖X‖²`) and thereby
introduces the `d+1`-st slot; each conversion to a Fejér slot squares the exponent and costs a
constant.  The result is the `(d+1)`-fold box-norm power at the slot window `arithIcc 1 (4HM+1)`
(the translate of `symIcc (2HM)`), with `s' = d+1`. -/
def MassToCube : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ e : ℕ, 1 ≤ e ∧ ∃ s' : ℕ, 2 ≤ s' ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (H M N : ℕ) (θ : ℝ) (f : ℤ → ℂ),
      1 ≤ H → 1 ≤ M → SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < θ → θ ≤ 1 →
      θ ≤ massAvg d H M N f →
      C * θ ^ e
        ≤ boxNormPow s' (fun _ => arithIcc 1 (massBoxCard H M)) (symIcc N) f

/-- The mean square of the cube mass over the slot box.  This is the quantity produced by the
Cauchy–Schwarz step `(E‖X‖)² ≤ E‖X‖²` from `massAvg`. -/
def massSq (d H M N : ℕ) (f : ℤ → ℂ) : ℝ :=
  (∑ n ∈ massBox d H M, ‖boxMass d (symIcc N) f n‖ ^ 2) / ((massBoxCard H M : ℝ) ^ d)

/-- **Piece 3b-i′ — the *squared* cube-mass average controls the box norm** (KKL §8, the Fejér
conversion of the `d + 1` slots, with the Cauchy–Schwarz step already performed).  This is the
genuinely analytic content of `MassToCube`; the equivalence
`massToCube_of_sq : SqToCube → MassToCube` (`SwapE/Reduce.lean`) uses only the elementary
Cauchy–Schwarz `massAvg_sq_le`. -/
def SqToCube : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ e : ℕ, 1 ≤ e ∧ ∃ s' : ℕ, 2 ≤ s' ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (H M N : ℕ) (θ : ℝ) (f : ℤ → ℂ),
      1 ≤ H → 1 ≤ M → SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < θ →
      θ ≤ massSq d H M N f →
      C * θ ^ e
        ≤ boxNormPow s' (fun _ => arithIcc 1 (massBoxCard H M)) (symIcc N) f

/-- **Piece 3b-ii — the window shrink** (KKL Lemma 3.5(vi) with `κ = D/L ≤ 1`, specialised): the
box norm at the long window `arithIcc 1 L` controls the box norm at any shorter window
`arithIcc 1 D`, `D ≤ L`, at the cost of a constant only (no datum dependence — this is exactly why
the endgame's conclusion carries no factor other than `M/(M+H)`). -/
def WindowShrink : Prop :=
  ∀ s : ℕ, 2 ≤ s → ∃ C : ℝ, 0 < C ∧
    ∀ (L D N : ℕ) (f : ℤ → ℂ), 1 ≤ D → D ≤ L → SupportIn f N →
      C * boxNormPow s (fun _ => arithIcc 1 L) (symIcc N) f
        ≤ uNormPow s (arithIcc 1 D) (symIcc N) f

/-- **Piece 3b — the uniformity norm from the cube mass.**  If the average of the cube mass over
the slot box is at least `θ ≤ 1`, then some Gowers uniformity norm of `f` at window `[D]` is at
least a power of `θ`, for every `D ≤ HM` with `D ≤ N`.  The proof is `MassToCube` (the
Cauchy–Schwarz/Fejér step) followed by `WindowShrink` (the trim `4HM+1 → D`), the root
`uNorm = uNormPow^{1/2^{s'}}` losing only the constant power `(C₂C₁)^{1/2^{s'}}`. -/
def UniformFromMass : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ e : ℕ, 1 ≤ e ∧ ∃ s' : ℕ, 2 ≤ s' ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (H M D N : ℕ) (θ : ℝ) (f : ℤ → ℂ),
      1 ≤ H → 1 ≤ M → 1 ≤ D → D ≤ H * M → D ≤ N →
      SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < θ → θ ≤ 1 →
      θ ≤ massAvg d H M N f →
      C * θ ^ e ≤ uNorm s' (arithIcc 1 D) (symIcc N) f

/-! ## 4. The node -/

open Classical in
/-- **The node `denseEndgame`** (P2P3_LEAD §3.6, node END), frozen in
`Submission/Work/Peluse/P2P3_STATEMENTS.lean.txt`.

The endgame of the dense concatenation: an averaging of the multiset box norms over generic
slopes gives, at window `[D]` with `D ≤ HM`, a `U^{s'}` bound whose only regime factor is
`M/(M+H)` (a power of `γ` in the application, since `H ≲ M` there). -/
def DenseEndgame : Prop :=
  ∀ d : ℕ, 1 ≤ d → ∃ K : ℕ, 1 ≤ K ∧ ∃ s' : ℕ, 2 ≤ s' ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (q₁ q₂ : Ω → Fin d → ℤ) (G : Finset Ω)
      (H M D N : ℕ) (η δ : ℝ) (f : ℤ → ℂ),
      1 ≤ H → 1 ≤ M → 1 ≤ D → D ≤ H * M → D ≤ N →
      SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < η → η ≤ 1 → 0 < δ →
      (∀ ω k, |q₁ ω k| ≤ (H : ℤ) ∧ |q₂ ω k| ≤ (H : ℤ)) →
      (∀ ω ∈ G, ∀ k, genPair H η (q₁ ω k) (q₂ ω k)) →
      (((Finset.univ \ G).card : ℝ) ≤ δ / 2 * (Fintype.card Ω : ℝ)) →
      δ ≤ avg (fun ω : Ω => pbox d (q₁ ω) (q₂ ω) M (symIcc N) f) →
      C * (δ * η ^ 2 * (M : ℝ) / ((M : ℝ) + (H : ℝ))) ^ K
        ≤ uNorm s' (arithIcc 1 D) (symIcc N) f

end

end Work.Peluse.SwapE
