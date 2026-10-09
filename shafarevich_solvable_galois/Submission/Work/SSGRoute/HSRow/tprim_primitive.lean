import Mathlib
import Submission.Work.SSGRoute.HSRow.TransgressionDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `d¹ (tprim σ c β) = c` on `I × I`

The conjugate `σ`-translate of the graph of `-β` is again a primitive of `c|_{I × I}`.

Write `ρ = res k K` for the restriction `G_k →* Gal(K/k)`, so that `M` is a
`Gal(K/k)`-module.  The transgression cochain

  `tprim σ c β x = ρ(σ) • β (σ⁻¹ x σ) - c σ (σ⁻¹ x σ) + ρ(x) • c σ σ⁻¹ - c (x σ) σ⁻¹ + c 1 1`

splits as `U x + S x` with

  `U x = ρ(σ) • β (σ⁻¹ x σ) - c σ (σ⁻¹ x σ)`,
  `S x = ρ(x) • c σ σ⁻¹ - c (x σ) σ⁻¹ + c 1 1`,

and the two halves are independent group-cohomology computations
(`d1_tprimU_general`, `d1_tprimS_general` below, stated over an arbitrary group hom
`ρ : Γ →* G` and *not* using anything about number fields):

* for `n, m ∈ I`, writing `y = σ⁻¹ n σ`, `z = σ⁻¹ m σ`, one has `n σ = σ y`, `m σ = σ z`,
  `σ⁻¹ (n m) σ = y z`; collapsing the `β`-terms to `ρ(σ) • c y z` with `hβ` at `(y,z)` and
  telescoping the `c`-terms with `hc` at `(σ,y,z)` and `(n,σ,z)` gives
  `d¹ U (n,m) = c n (m σ) - c n σ`;
* telescoping the `c`-terms with `hc` at `(n,mσ,σ⁻¹)`, `(n,σ,σ⁻¹)` and using
  `c (g,1) = ρ(g) • c (1,1)` (from `hc` at `(g,1,1)`) to cancel the junk `c 1 1` terms gives
  `d¹ S (n,m) = c n m - c n (m σ) + c n σ`.

The two pieces add up to `c n m`, which is the lemma `tprim_primitive` (the assembly is
the final theorem below).
-/

namespace Work.SSGRoute.HSRow

open Classical

/-- **The `U` half.**  For a `2`-cocycle `c` on `D` and a primitive `β` of `c|_I`, the
`β`-part `U x = ρ(σ) • β (σ⁻¹ x σ) - c σ (σ⁻¹ x σ)` of the conjugate primitive has
`d¹ U (n,m) = c n (m σ) - c n σ` for `n, m ∈ I`. -/
theorem d1_tprimU_general {Γ G M : Type*} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M]
    (ρ : Γ →* G) (D I : Subgroup Γ) (σ : Γ) (hσ : σ ∈ D) (hI : I ≤ D)
    (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I)
    (c : Γ → Γ → M)
    (hc : ∀ g ∈ D, ∀ h ∈ D, ∀ l ∈ D, ρ g • c h l - c (g*h) l + c g (h*l) - c g h = 0)
    (β : Γ → M)
    (hβ : ∀ n ∈ I, ∀ m ∈ I, ρ n • β m - β (n*m) + β n = c n m) :
    ∀ n ∈ I, ∀ m ∈ I,
      ρ n • (ρ σ • β (σ⁻¹*m*σ) - c σ (σ⁻¹*m*σ))
        - (ρ σ • β (σ⁻¹*(n*m)*σ) - c σ (σ⁻¹*(n*m)*σ))
        + (ρ σ • β (σ⁻¹*n*σ) - c σ (σ⁻¹*n*σ))
      = c n (m*σ) - c n σ := by
  intro n hn m hm
  have hyI : σ⁻¹ * n * σ ∈ I := hnorm2 n hn
  have hzI : σ⁻¹ * m * σ ∈ I := hnorm2 m hm
  set y := σ⁻¹ * n * σ with hy
  set z := σ⁻¹ * m * σ with hz
  have hyI' : y ∈ I := by rw [hy]; exact hyI
  have hzI' : z ∈ I := by rw [hz]; exact hzI
  have hyD : y ∈ D := hI hyI'
  have hzD : z ∈ D := hI hzI'
  have hnD : n ∈ D := hI hn
  have hmiddle : σ⁻¹ * (n*m) * σ = y * z := by rw [hy, hz]; group
  have hnσ : n * σ = σ * y := by rw [hy]; group
  have hσz : σ * z = m * σ := by rw [hz]; group
  rw [hmiddle]
  have hconj1 : ρ n • (ρ σ • β z) = ρ σ • (ρ y • β z) := by
    rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul, hnσ]
  have hβyz : ρ y • β z - β (y*z) + β y = c y z := hβ y hyI' z hzI'
  have hβσ : ρ σ • (ρ y • β z - β (y*z) + β y) = ρ σ • c y z := by rw [hβyz]
  have key1 : ρ n • (ρ σ • β z - c σ z) - (ρ σ • β (y*z) - c σ (y*z)) + (ρ σ • β y - c σ y)
      = ρ σ • (ρ y • β z) - ρ σ • β (y*z) + ρ σ • β y - ρ n • c σ z + c σ (y*z) - c σ y := by
    rw [smul_sub, hconj1]; abel
  rw [key1, ← smul_sub, ← smul_add, hβσ]
  have h1' : c σ (y*z) - c σ y = c (n*σ) z - ρ σ • c y z := by
    have h := hc σ hσ y hyD z hzD
    rw [show σ * y = n * σ from hnσ.symm] at h
    refine sub_eq_zero.mp ?_
    rw [← h]; abel
  have h2' : c (n*σ) z - ρ n • c σ z = c n (m*σ) - c n σ := by
    have h := hc n hnD σ hσ z hzD
    rw [hσz] at h
    have hh : ρ n • c σ z - c (n*σ) z = c n σ - c n (m*σ) := by
      refine sub_eq_zero.mp ?_
      rw [← h]; abel
    rw [show c (n*σ) z - ρ n • c σ z = -(ρ n • c σ z - c (n*σ) z) from by abel, hh]
    abel
  rw [show ρ σ • c y z - ρ n • c σ z + c σ (y*z) - c σ y
        = (ρ σ • c y z - ρ n • c σ z) + (c σ (y*z) - c σ y) from by abel]
  rw [h1']
  rw [show (ρ σ • c y z - ρ n • c σ z) + (c (n*σ) z - ρ σ • c y z)
        = c (n*σ) z - ρ n • c σ z from by abel]
  rw [h2']

/-- **The `S` half.**  The `c`-part `S x = ρ(x) • c σ σ⁻¹ - c (x σ) σ⁻¹ + c 1 1` of the
conjugate primitive has `d¹ S (n,m) = c n m - c n (m σ) + c n σ` for `n, m ∈ I`. -/
theorem d1_tprimS_general {Γ G M : Type*} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M]
    (ρ : Γ →* G) (D I : Subgroup Γ) (σ : Γ) (hσ : σ ∈ D) (hI : I ≤ D)
    (c : Γ → Γ → M)
    (hc : ∀ g ∈ D, ∀ h ∈ D, ∀ l ∈ D, ρ g • c h l - c (g*h) l + c g (h*l) - c g h = 0) :
    ∀ n ∈ I, ∀ m ∈ I,
      ρ n • (ρ m • c σ σ⁻¹ - c (m*σ) σ⁻¹ + c 1 1)
        - (ρ (n*m) • c σ σ⁻¹ - c ((n*m)*σ) σ⁻¹ + c 1 1)
        + (ρ n • c σ σ⁻¹ - c (n*σ) σ⁻¹ + c 1 1)
      = c n m - c n (m*σ) + c n σ := by
  intro n hn m hm
  have hnD : n ∈ D := hI hn
  have hmD : m ∈ D := hI hm
  have hmσD : m * σ ∈ D := mul_mem hmD hσ
  have hsD : σ⁻¹ ∈ D := inv_mem hσ
  have h1D : (1 : Γ) ∈ D := one_mem D
  -- `c (g,1) = ρ(g) • c (1,1)`
  have hA : ρ n • c 1 1 = c n 1 := by
    have h := hc n hnD 1 h1D 1 h1D
    have h' : ρ n • c 1 1 - c n 1 = 0 := by simpa using h
    exact sub_eq_zero.mp h'
  -- `hc` at `(n, m σ, σ⁻¹)`
  have hB : ρ n • c (m * σ) σ⁻¹ = c ((n * m) * σ) σ⁻¹ - c n m + c n (m * σ) := by
    have h := hc n hnD (m * σ) hmσD σ⁻¹ hsD
    simp only [mul_inv_cancel, mul_one, mul_assoc] at h
    rw [show n * (m * σ) = (n * m) * σ from (mul_assoc n m σ).symm] at h
    refine sub_eq_zero.mp ?_
    rw [← h]; abel
  -- `hc` at `(n, σ, σ⁻¹)`
  have hC : ρ n • c σ σ⁻¹ = c (n * σ) σ⁻¹ - c n 1 + c n σ := by
    have h := hc n hnD σ hσ σ⁻¹ hsD
    simp only [mul_inv_cancel] at h
    refine sub_eq_zero.mp ?_
    rw [← h]; abel
  have hD : ρ n • ρ m • c σ σ⁻¹ = ρ (n * m) • c σ σ⁻¹ := by
    rw [← mul_smul, ← map_mul]
  rw [smul_add, smul_sub, hD, hA, hB, hC]
  abel

/-- The conjugate `σ`-translate of the graph of `-β` is again a primitive of `c|_{I × I}`:
`d¹ (tprim σ c β) = c` on `I × I`.  Proof: write `y = σ⁻¹nσ`, `z = σ⁻¹mσ` (both in `I`), collapse the
`β`-terms to `ρ(σ) • c y z` with `hβ`, then telescope the `c`-terms with the cocycle identities of
`hc` at `(σ,y,z)`, `(n,σ,z)`, `(n,σ,σ⁻¹)`, `(n,mσ,σ⁻¹)`, using `c (g,1) = ρ(g) • c (1,1)` (from
`hc` at `(g,1,1)`) to cancel the junk `c 1 1` terms. -/
theorem tprim_primitive
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (D I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω)
    (hσ : σ ∈ D) (hI : I ≤ D) (hnorm2 : ∀ n ∈ I, σ⁻¹ * n * σ ∈ I)
    (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)
    (hc : SSGRoute.IsCocycle2On p k Ω K M D c)
    (β : (Ω ≃ₐ[k] Ω) → M)
    (hβ : ∀ n ∈ I, ∀ m ∈ I, SSGRoute.res k K n • β m - β (n * m) + β n = c n m) :
    ∀ n ∈ I, ∀ m ∈ I,
      SSGRoute.res k K n • tprim p k Ω K M σ c β m - tprim p k Ω K M σ c β (n * m)
        + tprim p k Ω K M σ c β n = c n m := by
  intro n hn m hm
  -- `tprim σ c β = U + S` with the two halves above
  let U : (Ω ≃ₐ[k] Ω) → M := fun x =>
    SSGRoute.res k K σ • β (σ⁻¹ * x * σ) - c σ (σ⁻¹ * x * σ)
  let S : (Ω ≃ₐ[k] Ω) → M := fun x =>
    SSGRoute.res k K x • c σ σ⁻¹ - c (x * σ) σ⁻¹ + c 1 1
  have hsplit : ∀ x : Ω ≃ₐ[k] Ω, tprim p k Ω K M σ c β x = U x + S x := by
    intro x
    simp only [tprim_apply]
    dsimp only [U, S]
    abel
  have hU : SSGRoute.res k K n • U m - U (n * m) + U n = c n (m * σ) - c n σ := by
    dsimp only [U]
    exact d1_tprimU_general (SSGRoute.res k K) D I σ hσ hI hnorm2 c hc β hβ n hn m hm
  have hS : SSGRoute.res k K n • S m - S (n * m) + S n
      = c n m - c n (m * σ) + c n σ := by
    dsimp only [S]
    exact d1_tprimS_general (SSGRoute.res k K) D I σ hσ hI c hc n hn m hm
  rw [hsplit m, hsplit (n * m), hsplit n, smul_add]
  rw [show SSGRoute.res k K n • U m + SSGRoute.res k K n • S m
        - (U (n * m) + S (n * m)) + (U n + S n)
      = (SSGRoute.res k K n • U m - U (n * m) + U n)
        + (SSGRoute.res k K n • S m - S (n * m) + S n) from by abel]
  rw [hU, hS]
  abel

end Work.SSGRoute.HSRow
