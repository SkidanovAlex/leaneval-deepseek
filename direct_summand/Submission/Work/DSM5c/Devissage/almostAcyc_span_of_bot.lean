import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5c.Devissage.almostAcyc_span_pow

/-!
# DSM5c — the `⊥ ↦ (u)` dévissage for `AlmostAcyc`

Let `W` be a commutative ring, `p` a prime, `ϖ : ℕ → W` a compatible system of `p`-power roots
(`ϖ (k+1) ^ p = ϖ k`), and `K` a cochain complex of `W`-modules in nonnegative degrees with a
cocycle coaugmentation `e : W → K⁰`.  If `u` is a non-zero-divisor on every term `K^q` and the
augmented complex `W → K` is `ϖ`-almost acyclic (i.e. `AlmostAcyc ϖ ⊥ K e`: all cohomology is
killed by every `ϖ k`), then it is `ϖ`-almost acyclic modulo the principal ideal `(u)`.

This is the "base change along `W ↠ W/u`" step of the M5c transport: `u` is a non-zero-divisor on
each `K^q`, so `Tor₁(W/u, K^q) = 0` and the cohomology of `K/u` is the cohomology of `K` tensored
with `W/u`; the `ϖ`-killing is preserved.  The elementary diagram chase produces two occurrences of
`ϖ j` per step (`ϖ j ^ 2 • z - d y ∈ (u)`), which are re-indexed along the root tower:
`ϖ k = ϖ (k+1) ^ p = ϖ (k+1) ^ (p-2) · ϖ (k+1) ^ 2` (using `p ≥ 2`), turning the square back into
`ϖ k` itself.  Nothing else about `u` is used.
-/

namespace Work.DSM5c.Devissage

open CategoryTheory

/-- Successive differentials of a cochain complex of modules compose to zero. -/
theorem d_comp_d_hom {W : Type*} [CommRing W] (K : CochainComplex (ModuleCat W) ℕ)
    (i j k : ℕ) (x : K.X i) : (K.d j k).hom ((K.d i j).hom x) = 0 := by
  have hd : (K.d i j ≫ K.d j k).hom x = 0 := by
    rw [HomologicalComplex.d_comp_d (C := K) i j k]
    simp
  rwa [ModuleCat.comp_apply] at hd

theorem almostAcyc_span_of_bot {p : ℕ} [Fact p.Prime] {W : Type*} [CommRing W]
    (ϖ : ℕ → W) (hroot : ∀ k, ϖ (k + 1) ^ p = ϖ k) (u : W)
    (K : CochainComplex (ModuleCat W) ℕ)
    (e : ModuleCat.of W W ⟶ K.X 0)
    (he : ∀ w : W, (K.d 0 1).hom (e.hom w) = 0)
    (hreg : ∀ q, IsSMulRegular (K.X q) u)
    (hK : DSMap.Mix2.AlmostAcyc ϖ ⊥ K e) :
    DSMap.Mix2.AlmostAcyc ϖ (Ideal.span {u}) K e := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  -- ## A dictionary for the zero ideal
  have hbot : ∀ (q : ℕ) (x : K.X q), x = 0 →
      x ∈ (⊥ : Ideal W) • (⊤ : Submodule W (K.X q)) := by
    intro q x hx
    rw [hx]
    simp
  have hbot' : ∀ (q : ℕ) (x : K.X q),
      x ∈ (⊥ : Ideal W) • (⊤ : Submodule W (K.X q)) → x = 0 := by
    intro q x hx
    rw [Submodule.bot_smul] at hx
    exact hx
  -- ## The re-indexing identity `ϖ (k+1) ^ (p-2) * ϖ (k+1) ^ 2 = ϖ k`
  have hpow : ∀ k : ℕ, ϖ (k + 1) ^ (p - 2) * ϖ (k + 1) ^ 2 = ϖ k := by
    intro k
    rw [← pow_add, Nat.sub_add_cancel hp2, hroot k]
  -- ## Clause (1): almost injectivity of `e` mod `(u)`
  have cl1 : ∀ w : W, e.hom w ∈ Ideal.span {u} • (⊤ : Submodule W (K.X 0)) →
      ∀ k, ϖ k * w ∈ Ideal.span {u} := by
    intro w hew k
    obtain ⟨z, hz⟩ := (mem_span_singleton_smul_top u (e.hom w)).mp hew
    -- `z` is a cycle
    have hdz : (K.d 0 1).hom z = 0 := by
      have h1 : u • (K.d 0 1).hom z = u • (0 : K.X 1) := by
        rw [smul_zero, ← map_smul, hz, he w]
      exact hreg 1 h1
    -- clause (2) of `hK` at the index `k+1`
    obtain ⟨w', hw'⟩ := hK.2.1 z (hbot 1 ((K.d 0 1).hom z) hdz) (k + 1)
    have hw'0 : ϖ (k + 1) • z = e.hom w' :=
      sub_eq_zero.mp (hbot' 0 (ϖ (k + 1) • z - e.hom w') hw')
    -- `e (ϖ(k+1) * w - u * w') = 0`
    have hee : e.hom (ϖ (k + 1) * w - u * w') = 0 := by
      have h1 : e.hom (ϖ (k + 1) * w) = u • (ϖ (k + 1) • z) := by
        rw [← smul_eq_mul (ϖ (k + 1)) w, map_smul, ← hz, smul_comm (ϖ (k + 1)) u z]
      have h2 : e.hom (u * w') = u • (ϖ (k + 1) • z) := by
        rw [← smul_eq_mul u w', map_smul, ← hw'0]
      rw [map_sub, h1, h2, sub_self]
    -- clause (1) of `hK` at the index `k+1`
    have h0 : ϖ (k + 1) * (ϖ (k + 1) * w - u * w') = 0 :=
      hK.1 (ϖ (k + 1) * w - u * w')
        (hbot 0 (e.hom (ϖ (k + 1) * w - u * w')) hee) (k + 1)
    have h0' : ϖ (k + 1) * (ϖ (k + 1) * w) = ϖ (k + 1) * (u * w') := by
      have h := h0
      rw [mul_sub] at h
      exact sub_eq_zero.mp h
    have hkey : ϖ (k + 1) ^ 2 * w = u * (ϖ (k + 1) * w') := by
      calc ϖ (k + 1) ^ 2 * w = ϖ (k + 1) * (ϖ (k + 1) * w) := by ring
        _ = ϖ (k + 1) * (u * w') := h0'
        _ = u * (ϖ (k + 1) * w') := by ring
    -- re-index
    refine (mem_span_singleton_iff u (ϖ k * w)).mpr
      ⟨ϖ (k + 1) ^ (p - 2) * (ϖ (k + 1) * w'), ?_⟩
    calc u * (ϖ (k + 1) ^ (p - 2) * (ϖ (k + 1) * w'))
        = ϖ (k + 1) ^ (p - 2) * (u * (ϖ (k + 1) * w')) := by ring
      _ = ϖ (k + 1) ^ (p - 2) * (ϖ (k + 1) ^ 2 * w) := by rw [← hkey]
      _ = ϖ k * w := by rw [← mul_assoc, hpow k]
  -- ## Clause (2): almost surjectivity of `e` on `H⁰` mod `(u)`
  have cl2 : ∀ z : K.X 0,
      (K.d 0 1).hom z ∈ Ideal.span {u} • (⊤ : Submodule W (K.X 1)) →
      ∀ k, ∃ w : W,
        ϖ k • z - e.hom w ∈ Ideal.span {u} • (⊤ : Submodule W (K.X 0)) := by
    intro z hz k
    obtain ⟨v, hv⟩ := (mem_span_singleton_smul_top u ((K.d 0 1).hom z)).mp hz
    -- `v` is a cycle
    have hdv : (K.d 1 2).hom v = 0 := by
      have h1 : u • (K.d 1 2).hom v = u • (0 : K.X 2) := by
        rw [smul_zero, ← map_smul, hv]
        exact d_comp_d_hom K 0 1 2 z
      exact hreg 2 h1
    -- clause (3) of `hK` at `q = 0`, index `k+1`
    obtain ⟨y₀, hy₀⟩ := hK.2.2 0 v (hbot 2 ((K.d 1 2).hom v) hdv) (k + 1)
    have hy₀0 : (K.d 0 1).hom y₀ = ϖ (k + 1) • v :=
      (sub_eq_zero.mp
        (hbot' 1 (ϖ (k + 1) • v - (K.d 0 1).hom y₀) hy₀)).symm
    -- `ϖ(k+1) • z - u • y₀` is a cycle
    have hξ : (K.d 0 1).hom (ϖ (k + 1) • z - u • y₀) = 0 := by
      rw [map_sub, map_smul, map_smul, ← hv, hy₀0, smul_comm (ϖ (k + 1)) u v, sub_self]
    -- clause (2) of `hK` at the index `k+1`
    obtain ⟨w₁, hw₁⟩ := hK.2.1 (ϖ (k + 1) • z - u • y₀)
      (hbot 1 ((K.d 0 1).hom (ϖ (k + 1) • z - u • y₀)) hξ) (k + 1)
    have hw₁0 : ϖ (k + 1) • (ϖ (k + 1) • z - u • y₀) = e.hom w₁ :=
      sub_eq_zero.mp (hbot' 0 (ϖ (k + 1) • (ϖ (k + 1) • z - u • y₀) - e.hom w₁) hw₁)
    have hkey : ϖ (k + 1) ^ 2 • z - e.hom w₁ = u • (ϖ (k + 1) • y₀) := by
      have hp2' : ϖ (k + 1) ^ 2 • z = ϖ (k + 1) • (ϖ (k + 1) • z) := by
        rw [pow_two, smul_smul]
      rw [hp2', ← hw₁0, smul_sub, smul_comm (ϖ (k + 1)) u y₀]
      abel
    -- re-index
    refine ⟨ϖ (k + 1) ^ (p - 2) • w₁, ?_⟩
    refine (mem_span_singleton_smul_top u _).mpr
      ⟨ϖ (k + 1) ^ (p - 2) • (ϖ (k + 1) • y₀), ?_⟩
    calc u • (ϖ (k + 1) ^ (p - 2) • (ϖ (k + 1) • y₀))
        = ϖ (k + 1) ^ (p - 2) • (u • (ϖ (k + 1) • y₀)) := by
          rw [smul_comm u (ϖ (k + 1) ^ (p - 2)) (ϖ (k + 1) • y₀)]
      _ = ϖ (k + 1) ^ (p - 2) • (ϖ (k + 1) ^ 2 • z - e.hom w₁) := by rw [← hkey]
      _ = ϖ k • z - e.hom (ϖ (k + 1) ^ (p - 2) • w₁) := by
            rw [smul_sub, smul_smul, hpow k, ← map_smul]
  -- ## Clause (3): `H^q` (`q ≥ 0`) almost zero mod `(u)`
  have cl3 : ∀ (q : ℕ) (z : K.X (q + 1)),
      (K.d (q + 1) (q + 2)).hom z ∈ Ideal.span {u} • (⊤ : Submodule W (K.X (q + 2))) →
      ∀ k, ∃ y : K.X q,
        ϖ k • z - (K.d q (q + 1)).hom y ∈
          Ideal.span {u} • (⊤ : Submodule W (K.X (q + 1))) := by
    intro q z hz k
    obtain ⟨v, hv⟩ := (mem_span_singleton_smul_top u ((K.d (q + 1) (q + 2)).hom z)).mp hz
    -- `v` is a cycle
    have hdv : (K.d (q + 2) (q + 3)).hom v = 0 := by
      have h1 : u • (K.d (q + 2) (q + 3)).hom v = u • (0 : K.X (q + 3)) := by
        rw [smul_zero, ← map_smul, hv]
        exact d_comp_d_hom K (q + 1) (q + 2) (q + 3) z
      exact hreg (q + 3) h1
    obtain ⟨y₀, hy₀⟩ := hK.2.2 (q + 1) v (hbot (q + 3) ((K.d (q + 2) (q + 3)).hom v) hdv)
      (k + 1)
    have hy₀0 : (K.d (q + 1) (q + 2)).hom y₀ = ϖ (k + 1) • v :=
      (sub_eq_zero.mp
        (hbot' (q + 2) (ϖ (k + 1) • v - (K.d (q + 1) (q + 2)).hom y₀) hy₀)).symm
    have hξ : (K.d (q + 1) (q + 2)).hom (ϖ (k + 1) • z - u • y₀) = 0 := by
      rw [map_sub, map_smul, map_smul, ← hv, hy₀0, smul_comm (ϖ (k + 1)) u v, sub_self]
    obtain ⟨y₁, hy₁⟩ := hK.2.2 q (ϖ (k + 1) • z - u • y₀)
      (hbot (q + 2) ((K.d (q + 1) (q + 2)).hom (ϖ (k + 1) • z - u • y₀)) hξ) (k + 1)
    have hy₁0 : (K.d q (q + 1)).hom y₁ = ϖ (k + 1) • (ϖ (k + 1) • z - u • y₀) :=
      (sub_eq_zero.mp (hbot' (q + 1) (ϖ (k + 1) • (ϖ (k + 1) • z - u • y₀)
        - (K.d q (q + 1)).hom y₁) hy₁)).symm
    have hkey : ϖ (k + 1) ^ 2 • z - (K.d q (q + 1)).hom y₁ = u • (ϖ (k + 1) • y₀) := by
      have hp2' : ϖ (k + 1) ^ 2 • z = ϖ (k + 1) • (ϖ (k + 1) • z) := by
        rw [pow_two, smul_smul]
      rw [hp2', hy₁0, smul_sub, smul_comm (ϖ (k + 1)) u y₀]
      abel
    refine ⟨ϖ (k + 1) ^ (p - 2) • y₁, ?_⟩
    refine (mem_span_singleton_smul_top u _).mpr
      ⟨ϖ (k + 1) ^ (p - 2) • (ϖ (k + 1) • y₀), ?_⟩
    calc u • (ϖ (k + 1) ^ (p - 2) • (ϖ (k + 1) • y₀))
        = ϖ (k + 1) ^ (p - 2) • (u • (ϖ (k + 1) • y₀)) := by
          rw [smul_comm u (ϖ (k + 1) ^ (p - 2)) (ϖ (k + 1) • y₀)]
      _ = ϖ (k + 1) ^ (p - 2) • (ϖ (k + 1) ^ 2 • z - (K.d q (q + 1)).hom y₁) := by
            rw [← hkey]
      _ = ϖ k • z - (K.d q (q + 1)).hom (ϖ (k + 1) ^ (p - 2) • y₁) := by
            rw [smul_sub, smul_smul, hpow k, ← map_smul]
  exact ⟨cl1, cl2, cl3⟩

end Work.DSM5c.Devissage
