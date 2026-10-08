import Mathlib
import Submission.Work.ZassenhausSuzuki.SzAuto.Vtriv
import Submission.Work.ZassenhausSuzuki.SzA.hLamHom_injective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Hua subgroup of `Aut(A(K,θ))` recovers the torus `Λ = Kˣ`

`Aut_V_action_scalar` produces, for an automorphism `z` of Higman's group
`A = A(GF(2ⁿ), θ)` of order `2ⁿ - 1`, a unit `λ` of `K = GF(2ⁿ)` with
`z x * (h_λ x)⁻¹ ∈ Z(A)` for all `x ∈ A`, i.e. `z ≡ h_λ` modulo the (normal) subgroup
`Vtriv θ ≤ Aut(A)` of automorphisms acting trivially on `A/Z(A)`.

This file proves the converse bookkeeping: if in addition `⟨z⟩ ⊓ Vtriv θ = ⊥` — which is exactly
the hypothesis that `z` acts *without non-trivial fixed points* on the involutions, cf.
`Vtriv_fixes_involution` — then `h_λ` has the same order as `z`, namely `2ⁿ - 1 = |Kˣ|`; hence
`λ` generates `Kˣ`.

The argument is a congruence computation in the finite group `Aut(A)`.  Write `h = h_λ = (hLamHom
θ) λ` and let `V = Vtriv θ`, a normal subgroup, and `q = 2ⁿ - 1`.

* `z * h⁻¹ ∈ V` is just a restatement of the hypothesis `hlam`.
* Since `V` is normal, `z * h⁻¹ ∈ V` implies `z ^ k * (h ^ k)⁻¹ ∈ V` for every `k`
  (conjugation by `z` plus multiplication).  In particular, as `h ^ q = 1` with `q = orderOf λ`,
  we get `z ^ q ∈ V`.
* `z ^ q ∈ ⟨z⟩ ⊓ V = ⊥`, so `z ^ q = 1`, i.e. `orderOf z = 2ⁿ - 1` divides `orderOf λ`.
* Conversely `orderOf λ ∣ |Kˣ| = 2ⁿ - 1`, because `GaloisField.card` gives `|GF(2ⁿ)| = 2ⁿ`.
* Hence `orderOf λ = 2ⁿ - 1 = |Kˣ|`, and a subgroup of `Kˣ` whose cardinality is that of `Kˣ`
  is everything: `⟨λ⟩ = Kˣ`.
-/

namespace Work.ZassenhausSuzuki.SzAuto

/-- **An automorphism of `A(GF(2ⁿ), θ)` of order `2ⁿ - 1` which differs from the torus element
`h_λ` only by an element acting trivially on the involutions forces `λ` to generate `Kˣ`.**

Equivalently: the torus automorphism attached to `z` by `aut_V_action_scalar` generates the full
torus `Λ ≅ Kˣ` of order `2ⁿ - 1`. -/
theorem zpowers_lam_eq_top {n : ℕ} (θ : GaloisField 2 n ≃+* GaloisField 2 n) (hn : n ≠ 0)
    (z : MulAut (Work.ZassenhausSuzuki.SzA (GaloisField 2 n) θ))
    (hz : orderOf z = 2 ^ n - 1)
    (hdisj : Subgroup.zpowers z ⊓ Work.ZassenhausSuzuki.Vtriv θ = ⊥)
    (lam : (GaloisField 2 n)ˣ)
    (hlam : ∀ x : Work.ZassenhausSuzuki.SzA (GaloisField 2 n) θ,
      z x * (Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 n) x)⁻¹
        ∈ Subgroup.center (Work.ZassenhausSuzuki.SzA (GaloisField 2 n) θ)) :
    Subgroup.zpowers lam = ⊤ := by
  -- `hlam` says `z ≡ h_λ` modulo `V = Vtriv θ`, the kernel of the action on `A/Z(A)`.
  have hmem : z * (Work.ZassenhausSuzuki.SzA.hLamHom θ lam)⁻¹
      ∈ Work.ZassenhausSuzuki.Vtriv θ := by
    intro x
    have key := hlam ((Work.ZassenhausSuzuki.SzA.hLamHom θ lam).symm x)
    rw [← Work.ZassenhausSuzuki.SzA.hLamHom_apply θ lam
        ((Work.ZassenhausSuzuki.SzA.hLamHom θ lam).symm x),
      MulEquiv.apply_symm_apply] at key
    simpa only [MulAut.mul_apply, MulAut.inv_apply] using key
  -- the congruence propagates to powers, since `V` is normal
  have hpowmem : ∀ k : ℕ,
      z ^ k * ((Work.ZassenhausSuzuki.SzA.hLamHom θ lam) ^ k)⁻¹
        ∈ Work.ZassenhausSuzuki.Vtriv θ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hconj : z * (z ^ k * ((Work.ZassenhausSuzuki.SzA.hLamHom θ lam) ^ k)⁻¹) * z⁻¹
          ∈ Work.ZassenhausSuzuki.Vtriv θ :=
        (Work.ZassenhausSuzuki.Vtriv_normal θ).conj_mem _ ih z
      have hprod := Subgroup.mul_mem _ hconj hmem
      have heq : z ^ (k + 1) * ((Work.ZassenhausSuzuki.SzA.hLamHom θ lam) ^ (k + 1))⁻¹ =
          (z * (z ^ k * ((Work.ZassenhausSuzuki.SzA.hLamHom θ lam) ^ k)⁻¹) * z⁻¹) *
            (z * (Work.ZassenhausSuzuki.SzA.hLamHom θ lam)⁻¹) := by
        group
      rw [heq]
      exact hprod
  have hpow : (Work.ZassenhausSuzuki.SzA.hLamHom θ lam) ^ orderOf lam = 1 := by
    rw [← map_pow (Work.ZassenhausSuzuki.SzA.hLamHom θ), pow_orderOf_eq_one, map_one]
  -- therefore `z ^ orderOf λ` lies in `V`, and hence is `1` by disjointness
  have hzd : z ^ orderOf lam ∈ Work.ZassenhausSuzuki.Vtriv θ := by
    have h1 := hpowmem (orderOf lam)
    rwa [hpow, inv_one, mul_one] at h1
  have hz1 : z ^ orderOf lam = 1 := by
    have h2 : z ^ orderOf lam ∈ Subgroup.zpowers z ⊓ Work.ZassenhausSuzuki.Vtriv θ :=
      ⟨Subgroup.mem_zpowers_iff.mpr ⟨(orderOf lam : ℤ), by simp⟩, hzd⟩
    rw [hdisj] at h2
    simpa using h2
  have hdvd : orderOf z ∣ orderOf lam := orderOf_dvd_iff_pow_eq_one.mpr hz1
  -- `|Kˣ| = 2ⁿ - 1`
  have hcard : Nat.card ((GaloisField 2 n)ˣ) = 2 ^ n - 1 := by
    rw [Nat.card_units, GaloisField.card 2 n hn]
  have hdvd2 : orderOf lam ∣ 2 ^ n - 1 := by
    rw [← hcard]
    exact orderOf_dvd_natCard lam
  have hlam_ord : orderOf lam = 2 ^ n - 1 := by
    have h1 : 2 ^ n - 1 ∣ orderOf lam := by rw [← hz]; exact hdvd
    exact (Nat.dvd_antisymm h1 hdvd2).symm
  -- an element of order `|Kˣ|` generates `Kˣ`
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, hcard]
  exact hlam_ord

end Work.ZassenhausSuzuki.SzAuto
