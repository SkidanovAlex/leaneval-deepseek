import Submission.Work.SSGRoute.E7Fin.canonLogData
import Submission.NK.LocalInputs.PowerQuotient.Lam
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Γ`-equivariance of the `p`-adic logarithm of the principal units

Lane `Work.SSGRoute.coker_obstruction_pt`, obligation (LOG) of
`E7Fin/PING_session22_localLevelField_and_C_targets.md` §2.1 / §7 step 4.

`NK.LocalInputs.PowerQuotient.lamFun D hp hres : U¹ → 𝔭.adicCompletion K` is the logarithm of a
principal unit (`log (u ^ p ^ e) / p ^ e`, `e = ram + M`).  Its `Γ`-equivariance,
`lamFun (σ u) = σ (lamFun u)`, is *false* for a general `LogData` (the axioms do not pin the
normalisation of `exp`), but true for the canonical, `HasSum`-pinned pair, where it follows from
`E7Fin.CanonLogData.log_map` (the equivariance of the canonical logarithm):

* `exp` is pinned by its series, so any continuous valuation-preserving ring automorphism `τ` of the
  completion commutes with it (`E7Fin.CanonLogData.exp_map`);
* hence `τ` commutes with `log` on the disk (`E7Fin.CanonLogData.log_map`);
* the powers `u ^ p ^ e` and the division by `p ^ e` then commute with `τ` as well, because `τ`
  fixes `ℚ` (so `τ p = p`).

The transport of `u` along `τ` is formulated *elementwise* — the consumer (the local Galois action
at a fixed place) supplies the identification `↑v = τ ↑u` of principal units — so no automorphism
of the ring of integers has to be built.

## Main result

* **`E7Fin.lamFun_map_ringEquiv`** — `lamFun D hp hres v = τ (lamFun D hp hres u)` whenever
  `↑v = τ ↑u`.
-/

namespace Work.SSGRoute.E7Fin

open NK.LocalInputs.PowerQuotient

variable {K : Type*} [Field K] [NumberField K]

/-- **LOG step 4 (equivariance of the logarithm).**  For the canonical logarithm, a continuous
valuation-preserving ring automorphism `τ` of the completion commutes with `lamFun`: if `v` (a
principal unit) is the image of `u` under `τ` on the level of the completion, then
`lamFun D hp hres v = τ (lamFun D hp hres u)`. -/
theorem lamFun_map_ringEquiv {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {p M : ℕ} (D : CanonLogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (τ : 𝔭.adicCompletion K ≃+* 𝔭.adicCompletion K) (hτc : Continuous τ)
    (hτv : ∀ x : 𝔭.adicCompletion K, vv 𝔭 (τ x) = vv 𝔭 x)
    (u v : ↥(pu 𝔭 1))
    (hv : ((v : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K)
      = τ (((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K))) :
    lamFun D.toLogData hp hres v = τ (lamFun D.toLogData hp hres u) := by
  set W : 𝔭.adicCompletion K :=
    (((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K)) ^ p ^ (lamK 𝔭 M) with hW
  have hw : Disk 𝔭 M W := by
    have h := (mem_pu_iff_val 𝔭 M
      ((u : (𝔭.adicCompletionIntegers K)ˣ) ^ p ^ (lamK 𝔭 M))).mp
      (deep_pow_mem' (K := K) (𝔭 := 𝔭) (M := M) (p := p) hp hres u.2)
    rw [Units.val_pow_eq_pow_val] at h
    exact h
  have hpow : (((v : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K)) ^ p ^ (lamK 𝔭 M)
      = τ W := by
    rw [hv, hW]
    simp only [map_pow]
  have hlog : D.toLogData.log (τ W) = τ (D.toLogData.log W) :=
    (CanonLogData.log_map D τ hτc hτv W hw).symm
  rw [lamFun, lamFun, hpow, hlog, map_div₀]
  simp only [map_pow, map_natCast, hW]

/-- **`Λ = log U¹` is `Γ`-stable.**  If a continuous valuation-preserving ring automorphism `τ` of
the completion maps `U¹ = pu 𝔭 1` into itself (the `htrans` hypothesis; for the local Galois action
this is immediate), then it maps the lattice `Λ = Lam D hp hres = log U¹` into itself.  This is the
`Γ`-stability of `Λ` in LOG step 4. -/
theorem map_Lam_le {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {p M : ℕ} (D : CanonLogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (τ : 𝔭.adicCompletion K ≃+* 𝔭.adicCompletion K) (hτc : Continuous τ)
    (hτv : ∀ x : 𝔭.adicCompletion K, vv 𝔭 (τ x) = vv 𝔭 x)
    (htrans : ∀ u : ↥(pu 𝔭 1), ∃ v : ↥(pu 𝔭 1),
      ((v : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K)
        = τ (((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K))) :
    ∀ x ∈ Lam D.toLogData hp hres, τ x ∈ Lam D.toLogData hp hres := by
  rintro x ⟨u, rfl⟩
  obtain ⟨v, hv⟩ := htrans u
  exact ⟨v, lamFun_map_ringEquiv D hp hres τ hτc hτv u v hv⟩

/-- `lamFun 1 = 0`. -/
lemma lamFun_one {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {p M : ℕ} (D : CanonLogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    lamFun D.toLogData hp hres 1 = 0 :=
  (lamFun_eq_zero_iff D.toLogData hp hres 1).mpr (by simp)

/-- **`lamFun` is additive in the exponent**: `lamFun (u ^ n) = n • lamFun u` (from the
multiplicativity `lamFun_mul` of `NK/LocalInputs/PowerQuotient/Lam.lean`). -/
theorem lamFun_pow {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {p M : ℕ} (D : CanonLogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (u : ↥(pu 𝔭 1)) (n : ℕ) :
    lamFun D.toLogData hp hres (u ^ n) = n • lamFun D.toLogData hp hres u := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul]; exact lamFun_one D hp hres
  | succ k ih =>
      rw [pow_succ, lamFun_mul D.toLogData hp hres (u ^ k) u, ih, succ_nsmul]

/-- **Well-definedness of the induced map `U¹/(U¹)ᵖ → Λ/pΛ`.**  A `p`-th power of a principal unit
has logarithm divisible by `p` inside `Λ`: explicitly, `lamFun (w ^ p) = p • lamFun w` with
`lamFun w ∈ Λ`.  Hence `u ↦ lamFun u mod pΛ` is well defined on `U¹/(U¹)ᵖ`. -/
theorem lamFun_mem_pLam_of_mem_pow
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {p M : ℕ} (D : CanonLogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (w : ↥(pu 𝔭 1)) :
    ∃ x ∈ Lam D.toLogData hp hres, p • x = lamFun D.toLogData hp hres (w ^ p) :=
  ⟨lamFun D.toLogData hp hres w, lamFun_mem_Lam D.toLogData hp hres w,
    (lamFun_pow D hp hres w p).symm⟩

/-- **The `p`-power torsion lies in the kernel of the induced map.**  If the `p ^ (ram + M)`-th
power of a principal unit is `1` (in particular for a `p`-th root of unity in `U¹`), then its
logarithm vanishes: this is the `μ_p ⊆ ker` half of the exact sequence
`1 → μ_p → U¹ → Λ/pΛ`. -/
theorem lamFun_eq_zero_of_pow_eq_one
    {𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {p M : ℕ} (D : CanonLogData 𝔭 M) (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (u : ↥(pu 𝔭 1))
    (h : (((u : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletion K)) ^ p ^ (lamK 𝔭 M) = 1) :
    lamFun D.toLogData hp hres u = 0 :=
  (lamFun_eq_zero_iff D.toLogData hp hres u).mpr h

end Work.SSGRoute.E7Fin
