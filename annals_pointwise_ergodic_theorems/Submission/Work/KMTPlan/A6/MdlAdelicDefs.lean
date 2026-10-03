/-
# The adelic (mod-`Q`) vocabulary for the frozen-`t` core estimate (area A6, §8)

This module fixes the objects used to *reduce* the paper's Theorem `model-est-2` (estimate
`all-all-large-2` at `(p₁,p₂,p) = (2,2,1)`, Krause--Mirek--Tao, Annals 195 (2022), §8) for the
frozen-`t` slice `mdlSliceJ` of the model tuple to two inputs:

* the **adelic form** of the slice (its mod-`Q` Fourier decomposition together with its
  presentation as the diagonal of a `ZMod Q`-bilinear average), and
* the **`ZMod Q` variational chain** (`Hölder` on the probability space `ZMod Q`, the
  packet form of the paper's Corollary `bilinear-fkr`, and Cauchy--Schwarz in the real variable).

The transfer between the discrete `ℓ¹(ℤ; Vᵗ)`-norm and the continuous integral of the `ZMod Q`
average is `Work.KMTPlan.A6.diagonalVrSampling_le_of_band` (the quantitative Shannon sampling
comparison), and it consumes exactly the two objects defined here: the arc amplitudes
`A n a` (which give the lifted family `sliceLift A`) and the bilinear average `zmodAvg`.

Nothing here is postulated.
-/
import Mathlib
import Submission.Work.A6Big.Defs
import Submission.Work.KMTAreas.A7Rep.RephaseDefs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- The former import of `Submission.Work.KMTPlan.A6.MdlSliceCoreGainBig` here was *vestigial*: this
-- file uses none of `mdlSliceF/G`, `MdlSliceCoreGainMemLp`, `MdlSliceCoreGain*`.  Since 2026-10-03
-- the module `MdlSliceCoreGainBig` imports the copied §8 chain under `Submission/Work/A6Big/`,
-- whose declarations bear the *same* names as this file's; keeping the import therefore made this
-- module (and every consumer of it, i.e. most of the A6 lane) unbuildable with
-- `… has already been declared`.  The definitions that used to live in `MdlSliceCoreGainBig`
-- (`mdlSliceF`, `mdlSliceG`, `MdlSliceCoreGainMemLp`, `MdlSliceCoreGain_of_memLp`) now live in
-- `Submission.Work.A6Big.Defs`, imported here directly so consumers still see them transitively.

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7

/-! ## The scale split of the large-scale family

`mdlCore` requires the scale `N = ⌊a n⌋` to be larger than the doubly exponential cut
`splitCut ρ L = 2^{2^{uScale ρ L}}`, and the *band* of the `n`-th slice is of radius
`≈ 2^{max k₁ k₂}/N`.  The Shannon/decimation transfer applies to those scales for which this
radius is small compared with the spacing of the arithmetic frequencies, i.e. for

  `8 · arithQ ρ (max l₁ l₂) · 2^{lcL l₁ l₂ k₁ k₂ + 1} ≤ N`.

The remaining scales are the finitely many with `N` below this threshold; they are treated by a
crude per-scale estimate (`Work.KMTPlan.A6.MdlSliceBadPart`). -/

/-- The scales `N` on which the decimated sampling transfer applies: the band radius
`2^{L}/N` is at most `1/(8·Q)`, so that `β = 1/(8Q)` is an admissible band for the lift of the
arc amplitudes. -/
def goodScale (Q L : ℕ) (N : ℕ) : Prop := 8 * Q * 2 ^ (L + 1) ≤ N

instance (Q L N : ℕ) : Decidable (goodScale Q L N) := by unfold goodScale; infer_instance

/-! ## The arc amplitudes and the adelic lift -/

/-- **The adelic lift of a family with mod-`Q` arc amplitudes.**  It is the finite Fourier sum
`F n X ρ = ∑_{a<Q} e(aρ/Q) · 𝓕⁻(A n a)(X)`; on the diagonal `(X, ρ) = (x, x mod Q)` it is the
inverse Fourier transform of the generator `A n ·`.

This is literally the lift constructed in `Work.KMTPlan.A6.exists_adelicLift`, named so that the
reduction can refer to it. -/
noncomputable def sliceLift (Q : ℕ) (A : ℕ → ℕ → ℝ → ℂ) (n : ℕ) (X : ℝ) (ρ : ℤ) : ℂ :=
  ∑ a ∈ Finset.range Q,
    Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (ρ : ℂ) / (Q : ℂ)))
      * FourierTransformInv.fourierInv (A n a) X

/-- **The `ZMod Q` arithmetic averaging operator `A_{ZMod Q}`**:
`zmodAvg P u v θ = Q⁻¹ ∑_{y<Q} u(θ + y) · v(θ + P(y))`. -/
noncomputable def zmodAvg (P : ℤ[X]) (Q : ℕ) (u v : ZMod Q → ℂ) : ZMod Q → ℂ :=
  fun θ => (Q : ℂ)⁻¹ * ∑ y ∈ Finset.range Q, u (θ + (y : ZMod Q)) * v (θ + ((P.eval (y : ℤ) : ℤ) : ZMod Q))

/-! ## The `ZMod Q` variational data of a packet family -/

/-- **The `V^R([K]; ℓ²(ZMod Q))`-datum of a packet family `u`**: the supremum of the
`ℓ²(ZMod Q)`-norms together with the `R`-variation of the increments, i.e. the right hand side of
the paper's Corollary `bilinear-fkr` (as realised by `Work.KMTPlan.A6.BilinearFkrCyclic`). -/
noncomputable def VrLiftData (R : ℝ) (Q : ℕ) (u : ℕ → ZMod Q → ℂ) : ℝ≥0∞ :=
  (⨆ n : ℕ, eLpNorm (u n) 2 (Measure.count : Measure (ZMod Q))) +
    (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
      ENNReal.rpow (Finset.univ.sum fun i : Fin J =>
        ENNReal.rpow (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2
          (Measure.count : Measure (ZMod Q))) R) (1 / R))

/-! ## The three inputs of the reduction

`MdlSliceCoreGainMemLp` (hence `MdlSliceCoreGain`) is reduced to the following three
statements.  They are stated here as `Prop`s so that the reduction, the delegated proofs and the
final assembly share exactly the same text. -/

/-- **The `ZMod Q` variational chain** (the paper's §8 argument at `(p₁,p₂,p) = (2,2,1)`, on the
arithmetic side `ZMod Q`): from the arithmetic bilinear estimates of the packet form (`hbase` for
the individual packets, `hB1`/`hB2` for the increments) and the `L²(ℝ; V^R(ℓ²(ZMod Q)))`-bounds
on the two packet families, one obtains

`∫_ℝ Q⁻¹ ∑_{ρ<Q} V^r (B(u_n(X),v_n(X)))_n ≤ C·M·K_u·K_v`.

The proof is the chain of §8 after `form-2`: Hölder on the probability space `ZMod Q`
(`L¹ ≤ L^r`), the packet form of Corollary `bilinear-fkr` (realised by
`Work.KMTPlan.A6.BilinearFkrCyclic`), the pointwise bound `V^r ≤ sup + varPart` with
`sup_n |a_n| ≤ |a_0| + varPart`, and Cauchy--Schwarz in the `ℝ`-variable. -/
def ZModChainProp : Prop :=
  ∀ {r : NNReal} (hr : 1 ≤ r) {R : ℝ} (hR : 1 ≤ R) (hRr : R < (r : ℝ)),
    ∃ Cd : ℝ, 0 < Cd ∧
      ∀ {Q : ℕ} (hQ : 1 ≤ Q) {M Ku Kv : ℝ} (hM : 0 ≤ M) (hKu : 0 ≤ Ku) (hKv : 0 ≤ Kv)
      {B : (ZMod Q → ℂ) → (ZMod Q → ℂ) → (ZMod Q → ℂ)}
      (hadd₁ : ∀ e e' f : ZMod Q → ℂ, B (e + e') f = B e f + B e' f)
      (hadd₂ : ∀ e f f' : ZMod Q → ℂ, B e (f + f') = B e f + B e f')
      {u v : ℕ → ℝ → ZMod Q → ℂ}
      (humeas : ∀ (n : ℕ) (θ : ZMod Q), AEMeasurable (fun X : ℝ => u n X θ))
      (hvmeas : ∀ (n : ℕ) (θ : ZMod Q), AEMeasurable (fun X : ℝ => v n X θ))
      (hbase : ∀ (X : ℝ) (n : ℕ),
        eLpNorm (fun ρ : ZMod Q => B (u n X) (v n X) ρ) (r : ENNReal)
            (Measure.count : Measure (ZMod Q))
          ≤ ENNReal.ofReal M * eLpNorm (u n X) 2 (Measure.count : Measure (ZMod Q))
              * eLpNorm (v n X) 2 (Measure.count : Measure (ZMod Q)))
      (hB1 : ∀ (X : ℝ) (m n l : ℕ),
        eLpNorm (fun ρ : ZMod Q => B (u m X - u n X) (v l X) ρ) (r : ENNReal)
            (Measure.count : Measure (ZMod Q))
          ≤ ENNReal.ofReal M * eLpNorm (u m X - u n X) 2 (Measure.count : Measure (ZMod Q))
              * eLpNorm (v l X) 2 (Measure.count : Measure (ZMod Q)))
      (hB2 : ∀ (X : ℝ) (m n l : ℕ),
        eLpNorm (fun ρ : ZMod Q => B (u l X) (v m X - v n X) ρ) (r : ENNReal)
            (Measure.count : Measure (ZMod Q))
          ≤ ENNReal.ofReal M * eLpNorm (u l X) 2 (Measure.count : Measure (ZMod Q))
              * eLpNorm (v m X - v n X) 2 (Measure.count : Measure (ZMod Q)))
      (hSu : ∫⁻ X : ℝ, (VrLiftData R Q (fun n : ℕ => u n X)) ^ (2 : ℕ)
          ≤ ENNReal.ofReal (Ku ^ 2))
      (hSv : ∫⁻ X : ℝ, (VrLiftData R Q (fun n : ℕ => v n X)) ^ (2 : ℕ)
          ≤ ENNReal.ofReal (Kv ^ 2)),
      ∫⁻ X : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ ∈ Finset.range Q,
          variationalNorm r (fun n : ℕ => B (u n X) (v n X) ((ρ : ℤ) : ZMod Q))
        ≤ ENNReal.ofReal Cd * ENNReal.ofReal M * ENNReal.ofReal Ku * ENNReal.ofReal Kv

/-- **The adelic form of the good part of the frozen slice**: on the scales
`N = ⌊a n⌋` with `8·arithQ ρ (max l₁ l₂)·2^{lcL l₁ l₂ k₁ k₂ + 1} ≤ N` (the regime in which the band
`2^{lcL}/N` of the slice is narrow compared with the spacing `1/arithQ` of the arithmetic
frequencies), the slice is the diagonal of a `ZMod Q`-bilinear average of two band-limited packet
families, with the arithmetic bilinear constant `M` (whose size is `2^{-c·max(l₁,l₂)}` up to the
loss `Cin Λ`) and with `L²(ℝ;V^R(ℓ²(ZMod Q)))`-data `Ku`, `Kv` bounded by
`Cin Λ · lossWeight A ρ l₁ l₂ k₁ k₂ · ‖f‖₂` (resp. `‖g‖₂`). -/
def AdelicFormProp (P : ℤ[X]) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ Cin : NNReal → NNReal,
      ∀ (r : NNReal) (hr : 2 < r) (R : ℝ) (hR : 2 ≤ R) (hRr : R < (r : ℝ))
        (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal)
        (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (j₁ j₂ : ℤ)
        (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
        (f g : ℤ → ℂ),
        1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) →
        MemLp f 2 Measure.count → MemLp g 2 Measure.count →
        ∃ (F : ℕ → ℝ → ℤ → ℂ)
          (u v : ℕ → ℝ → ZMod (arithQ ρ (max l₁ l₂)) → ℂ) (M Ku Kv : ℝ),
          (∀ (n : ℕ) (ρ' : ℤ), Work.KMTAreas.A7Rep.HasRealFreqSupport (fun X : ℝ => F n X ρ')
              (Set.Icc (-(1 / (8 * (arithQ ρ (max l₁ l₂) : ℝ))))
                (1 / (8 * (arithQ ρ (max l₁ l₂) : ℝ))))) ∧
          (∀ (n : ℕ) (x : ℤ), F n (x : ℝ) (x % ((arithQ ρ (max l₁ l₂) : ℕ) : ℤ))
              = (if goodScale (arithQ ρ (max l₁ l₂)) (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
                  mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0)) ∧
          (∀ (n : ℕ) (X : ℝ) (ρ' : ℤ), F n X ρ'
              = zmodAvg P (arithQ ρ (max l₁ l₂)) (u n X) (v n X)
                  ((ρ' : ℤ) : ZMod (arithQ ρ (max l₁ l₂)))) ∧
          (0 ≤ M ∧ ENNReal.ofReal M
              ≤ (Cin Λ : ENNReal)
                * ENNReal.ofReal ((2 : ℝ) ^ (-(c * max (l₁ : ℝ) (l₂ : ℝ))))) ∧
          (ENNReal.ofReal Ku ≤ (Cin Λ : ENNReal)
              * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) * eLpNorm f 2 Measure.count) ∧
          (ENNReal.ofReal Kv ≤ (Cin Λ : ENNReal)
              * ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂) * eLpNorm g 2 Measure.count) ∧
          (∫⁻ X : ℝ, (VrLiftData R (arithQ ρ (max l₁ l₂)) (fun n : ℕ => u n X)) ^ (2 : ℕ)
              ≤ ENNReal.ofReal (Ku ^ 2)) ∧
          (∫⁻ X : ℝ, (VrLiftData R (arithQ ρ (max l₁ l₂)) (fun n : ℕ => v n X)) ^ (2 : ℕ)
              ≤ ENNReal.ofReal (Kv ^ 2)) ∧
          (∀ (n : ℕ) (θ : ZMod (arithQ ρ (max l₁ l₂))),
              AEMeasurable (fun X : ℝ => u n X θ)) ∧
          (∀ (n : ℕ) (θ : ZMod (arithQ ρ (max l₁ l₂))),
              AEMeasurable (fun X : ℝ => v n X θ)) ∧
          (∀ (X : ℝ) (n : ℕ),
            eLpNorm (fun ρ' : ZMod (arithQ ρ (max l₁ l₂)) =>
                zmodAvg P (arithQ ρ (max l₁ l₂)) (u n X) (v n X) ρ') (r : ENNReal)
                (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))
              ≤ ENNReal.ofReal M
                * eLpNorm (u n X) 2 (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))
                * eLpNorm (v n X) 2 (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))) ∧
          (∀ (X : ℝ) (m n l : ℕ),
            eLpNorm (fun ρ' : ZMod (arithQ ρ (max l₁ l₂)) =>
                zmodAvg P (arithQ ρ (max l₁ l₂)) (u m X - u n X) (v l X) ρ') (r : ENNReal)
                (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))
              ≤ ENNReal.ofReal M
                * eLpNorm (u m X - u n X) 2 (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))
                * eLpNorm (v l X) 2 (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))) ∧
          (∀ (X : ℝ) (m n l : ℕ),
            eLpNorm (fun ρ' : ZMod (arithQ ρ (max l₁ l₂)) =>
                zmodAvg P (arithQ ρ (max l₁ l₂)) (u l X) (v m X - v n X) ρ') (r : ENNReal)
                (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))
              ≤ ENNReal.ofReal M
                * eLpNorm (u l X) 2 (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂))))
                * eLpNorm (v m X - v n X) 2
                    (Measure.count : Measure (ZMod (arithQ ρ (max l₁ l₂)))))

/-- **The crude bound for the finitely many bad scales** (`N = ⌊a n⌋` below the threshold of
`goodScale`): the frozen slice truncated to those scales obeys the same shape of estimate, by the
per-scale bound `Work.KMTPlan.A6.MdlSliceSsuGain` (or the crude one) summed over the finitely many
scales, with the loss weight absorbing a constant. -/
def BadPartProp (P : ℤ[X]) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
      ∀ (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
        (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (j₁ j₂ : ℤ)
        (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
        (f g : ℤ → ℂ),
        1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) →
        MemLp f 2 Measure.count → MemLp g 2 Measure.count →
        eLpNorm (fun x : ℤ => variationalNorm r
            (fun n : ℕ => if ¬ goodScale (arithQ ρ (max l₁ l₂))
                (lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
                mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0))
          1 Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (lossWeight A ρ l₁ l₂ k₁ k₂
                * (2 : ℝ) ^ (-(c * (max (l₁ : ℝ) (l₂ : ℝ))))) *
              eLpNorm f 2 Measure.count *
              eLpNorm g 2 Measure.count

/-! ## Elementary facts -/

/-- **Real bookkeeping of the two loss weights.**  The exponential gain and the polynomial loss of
the good part (`2^{-c₀·max(l₁,l₂)} · lossWeight A₀²`, the square coming from the product of the two
packet bounds) and of the bad part (`lossWeight A₁ · 2^{-c₁·max(l₁,l₂)}`) are both absorbed by
`lossWeight (2A₀+A₁+1) · 2^{-(min c₀ c₁)/2·max(l₁,l₂)}`, with constant `1`: the loss exponent
`2A₀+A₁+1` is chosen so that both ratios `lossWeight A₀²/lossWeight (2A₀+A₁+1)` and
`lossWeight A₁/lossWeight (2A₀+A₁+1)` are `≤ 1` (the `lossWeight` argument `L = lmaxR` grows in
`k₁,k₂` while the gain only sees `max(l₁,l₂)`, so the loss exponent must dominate `2A₀`). -/
def LossAbsorbProp : Prop :=
  ∀ (A₀ A₁ c₀ c₁ : ℝ), 0 ≤ A₀ → 0 ≤ A₁ → 0 < c₀ → 0 < c₁ →
    ∀ ρ : ℝ, 0 < ρ → ∀ (l₁ l₂ k₁ k₂ : ℕ),
      (2 : ℝ) ^ (-(c₀ * max (l₁ : ℝ) (l₂ : ℝ))) * lossWeight A₀ ρ l₁ l₂ k₁ k₂ ^ 2
        ≤ (2 : ℝ) ^ (-((min c₀ c₁) / 2) * max (l₁ : ℝ) (l₂ : ℝ))
            * lossWeight (2 * A₀ + A₁ + 1) ρ l₁ l₂ k₁ k₂ ∧
      lossWeight A₁ ρ l₁ l₂ k₁ k₂ * (2 : ℝ) ^ (-(c₁ * max (l₁ : ℝ) (l₂ : ℝ)))
        ≤ (2 : ℝ) ^ (-((min c₀ c₁) / 2) * max (l₁ : ℝ) (l₂ : ℝ))
            * lossWeight (2 * A₀ + A₁ + 1) ρ l₁ l₂ k₁ k₂

/-- The modulus `Q` is positive in the settings of the reduction. -/
lemma one_le_arithQ (ρ : ℝ) (L : ℕ) : 1 ≤ arithQ ρ L := le_max_left _ _

/-- The residue `x mod Q` and `x` define the same element of `ZMod Q`. -/
lemma intCast_emod_zmod (Q : ℕ) (x : ℤ) : (((x % (Q : ℤ) : ℤ)) : ZMod Q) = (x : ZMod Q) := by
  have h : (x % (Q : ℤ)) + (Q : ℤ) * (x / (Q : ℤ)) = x := Int.emod_add_mul_ediv x (Q : ℤ)
  have h2 : (((x % (Q : ℤ) : ℤ)) : ZMod Q)
      + (((Q : ℤ) * (x / (Q : ℤ)) : ℤ) : ZMod Q) = (x : ZMod Q) := by
    rw [← h]
    norm_num
  simpa using h2

end

end Work.KMTPlan.A6
