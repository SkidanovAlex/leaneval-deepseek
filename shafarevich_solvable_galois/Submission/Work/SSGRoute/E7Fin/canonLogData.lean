import Mathlib.Topology.Connected.Separation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.Commons.Analysis.Nonarchimedean.exp_map_ringEquiv
import Submission.NK.LocalInputs.PowerQuotient.Setup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The *canonical* (`HasSum`-pinned) exponential/logarithm of a `p`-adic completion

`NK.LocalInputs.PowerQuotient.LogData 𝔭 M` (`Setup.lean:157`) records the properties of a
logarithm/exponential pair on the disk `{x | v x ≤ exp (-M)}` of `𝔭.adicCompletion K`, but it
deliberately does **not** record *which* pair: its axioms are satisfied by any group isomorphism
between the disk and its multiplicative image.  That is harmless for the additive/torsion
computations of the local-field chapter (`lamFun`, `Lam`, `natCard_*`), but it rules out
**equivariance**: `lamFun D hp hres (σ u) = σ (lamFun D hp hres u)` (the `Γ`-equivariance of the
`p`-adic logarithm, obligation LOG of `E7Fin/PING_session22_localLevelField_and_C_targets.md` §2.1)
is simply *false* for an arbitrary `D` (e.g. `exp` replaced by `x ↦ exp ((1 + p) x)`), because the
`LogData` axioms do not pin the normalisation.

This module repairs that by exposing the *canonical* pair: the one supplied by
`Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq`, whose `exp` is pinned by
the convergent series (`HasSum (fun n => x ^ n / n!) (exp x)`).  With that pin, `exp (x + y) =
exp x * exp y` is a *limit* statement, so any continuous ring endomorphism of the completion that
commutes with limits commutes with `exp` — which is the `Γ`-equivariance input of LOG.

## Main definitions

* `E7Fin.CanonLogData 𝔭 M` — a `LogData` together with the `HasSum` normalisation of `exp`.

## Main results

* `E7Fin.exists_canonLogData` — the canonical pair exists and is *unique* in its `exp` (a
  consequence of the `HasSum`, but not needed here).
-/

namespace Work.SSGRoute.E7Fin

open NK.LocalInputs.PowerQuotient (EDisk)

/-- **The canonical exponential/logarithm data on the disk of the completion.**  Extends
`LogData 𝔭 M` by the `HasSum` normalisation of the exponential:
`exp x = Σ_{n} x ^ n / n!`, which pins it among all `LogData` structures. -/
structure CanonLogData {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (M : ℕ)
    extends NK.LocalInputs.PowerQuotient.LogData 𝔭 M where
  /-- The exponential is the sum of the usual series on its disk of convergence. -/
  hasSum_exp : ∀ x : 𝔭.adicCompletion K,
    NK.LocalInputs.PowerQuotient.EDisk 𝔭 M x →
      HasSum (fun n : ℕ => x ^ n / ((n.factorial : ℕ) : 𝔭.adicCompletion K))
        (toLogData.exp x)

/-- **Existence of the canonical pair.**  The existential
`Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq` supplies `M ≥ 1`, an
exponential, a logarithm and — as its first clause, which `NK.LocalInputs.PowerQuotient.exists_logData`
discards — the `HasSum` normalisation of the exponential; together with the remaining clauses (which
are exactly the fields of `LogData`) this is a `CanonLogData 𝔭 M`. -/
theorem exists_canonLogData {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ M : ℕ, 1 ≤ M ∧ Nonempty (CanonLogData 𝔭 M) := by
  obtain ⟨M, hM, exp, log, h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
    Commons.Analysis.Nonarchimedean.exists_exp_log_adicCompletion_log_val_eq (K := K) 𝔭
  exact ⟨M, hM, ⟨
    { hM := hM
      exp := exp
      log := log
      exp_add := fun x y hx hy => h₄ x y hx hy
      exp_zero := h₃
      val_exp_sub_one := fun x hx => h₂ x hx
      exp_log := fun y hy => (h₅ y hy).2.2
      val_log := fun y hy => (h₅ y hy).2.1
      val_log_le := fun y hy => (h₅ y hy).1
      log_exp := fun x hx => h₆ x hx
      hasSum_exp := fun x hx => h₁ x hx }⟩⟩

/-- The `HasSum` normalisation pins the exponential: two `CanonLogData` structures on the same disk
with the same `M` have the same exponential (and hence, being mutually inverse on the disk, the same
logarithm). -/
theorem CanonLogData.exp_unique {K : Type*} [Field K] [NumberField K]
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {M : ℕ}
    (D₁ D₂ : CanonLogData 𝔭 M) :
    ∀ x, NK.LocalInputs.PowerQuotient.EDisk 𝔭 M x →
      D₁.toLogData.exp x = D₂.toLogData.exp x := by
  intro x hx
  exact (D₁.hasSum_exp x hx).unique (D₂.hasSum_exp x hx)

/-- **The `Γ`-equivariance of the canonical exponential** (LOG step 2 of
`E7Fin/PING_session22_localLevelField_and_C_targets.md` §3bis).  A continuous ring *automorphism*
`τ` of the completion which preserves the valuation commutes with the canonical exponential on its
disk.

This is the case needed for the local Galois action `Γ'' ≤ Gal(K_v/κ)` on the completion of `K` at a
place `𝔮`: `τ = localAutHom σ` is continuous and valuation preserving.  The proof is a direct
appeal to `Commons.Analysis.Nonarchimedean.exp_map_ringEquiv`, which is the same statement with the
`HasSum` hypothesis abstracted. -/
theorem CanonLogData.exp_map {K : Type*} [Field K] [NumberField K]
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {M : ℕ}
    (D : CanonLogData 𝔭 M) (τ : 𝔭.adicCompletion K ≃+* 𝔭.adicCompletion K)
    (hτc : Continuous τ) (hτv : ∀ x : 𝔭.adicCompletion K,
      NK.LocalInputs.PowerQuotient.vv 𝔭 (τ x) = NK.LocalInputs.PowerQuotient.vv 𝔭 x) :
    ∀ x, NK.LocalInputs.PowerQuotient.EDisk 𝔭 M x →
      τ (D.toLogData.exp x) = D.toLogData.exp (τ x) :=
  fun x hx => Commons.Analysis.Nonarchimedean.exp_map_ringEquiv 𝔭 M D.toLogData.exp
    D.hasSum_exp τ hτc hτv x hx

/-- **The `Γ`-equivariance of the canonical `p`-adic logarithm** (LOG step 3).  Same hypotheses as
`CanonLogData.exp_map`; the proof transports both sides through `exp` (mutually inverse with `log`
on the disk) and applies `E7Fin.CanonLogData.exp_inj`. -/
theorem CanonLogData.log_map {K : Type*} [Field K] [NumberField K]
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)} {M : ℕ}
    (D : CanonLogData 𝔭 M) (τ : 𝔭.adicCompletion K ≃+* 𝔭.adicCompletion K)
    (hτc : Continuous τ) (hτv : ∀ x : 𝔭.adicCompletion K,
      NK.LocalInputs.PowerQuotient.vv 𝔭 (τ x) = NK.LocalInputs.PowerQuotient.vv 𝔭 x) :
    ∀ y : 𝔭.adicCompletion K, NK.LocalInputs.PowerQuotient.Disk 𝔭 M y →
      τ (D.toLogData.log y) = D.toLogData.log (τ y) := by
  intro y hy
  have hτy : NK.LocalInputs.PowerQuotient.Disk 𝔭 M (τ y) := by
    rw [NK.LocalInputs.PowerQuotient.Disk] at hy ⊢
    rw [show τ y - 1 = τ (y - 1) by rw [map_sub, map_one], hτv (y - 1)]
    exact hy
  have h1 : D.toLogData.exp (τ (D.toLogData.log y)) = τ y := by
    rw [← D.exp_map τ hτc hτv (D.toLogData.log y) (D.toLogData.val_log_le y hy),
      D.toLogData.exp_log y hy]
  have h2 : D.toLogData.exp (D.toLogData.log (τ y)) = τ y := D.toLogData.exp_log (τ y) hτy
  have hτlog : NK.LocalInputs.PowerQuotient.EDisk 𝔭 M (τ (D.toLogData.log y)) := by
    rw [NK.LocalInputs.PowerQuotient.EDisk, hτv]
    exact D.toLogData.val_log_le y hy
  exact NK.LocalInputs.PowerQuotient.exp_inj D.toLogData hτlog
    (D.toLogData.val_log_le (τ y) hτy) (h1.trans h2.symm)

end Work.SSGRoute.E7Fin
