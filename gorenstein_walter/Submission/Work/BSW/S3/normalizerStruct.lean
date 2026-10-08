/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW)

# Bender §3.1 (ii): `N_G(C_G(x)) = C_G(x)(K ⊓ N_G(C_G(x)))`

Setting (Bender, *The Brauer–Suzuki–Wall theorem*, Illinois J. Math. **18** (1974) 229–235,
§3.1): `G` is a finite group satisfying `BSWHyps2 G t s K` (Bender's (i)–(iv)), `x ∉ H^G`
(`H = C_G(t) = K⟨s⟩`) is inverted by `t`, and

`F = C_G(x)`, `M = N_G(F)`.

The lemma proved here is clause (ii) of Bender's §3.1:

`M = F(K ⊓ M)`.

The proof.  `t ∈ M` and `t` inverts `F`, so `u := t * m * t` induces on `F` the *same*
conjugation as `m` does (conjugation by `t` is inversion on `F`, and inversion commutes with
every automorphism).  Hence for `m ∈ M` the element `c₀ = t * m * t * m⁻¹ = u * m⁻¹` acts
trivially on `F`, i.e. `c₀ ∈ C_G(F) = F`.  Now `|F|` is odd, so the squaring map of `F` is
surjective; choose `f ∈ F` with `f * f = m⁻¹ * c₀ * m`.  Then

`t * (m * f) * t = (t * m * t) * (t * f * t) = (c₀ * m) * f⁻¹ = (m * f * f) * f⁻¹ = m * f`,

so `m * f` is centralized by `t`, i.e. `m * f ∈ M ⊓ C_G(t) = M ⊓ K` (the latter equality is
`Work.BSW.S3.inf_normalizer_centralizer_t_eq_inf_K`).  Therefore every `m ∈ M` is
`(m * f) * f⁻¹ ∈ (K ⊓ M)F`, giving `M ≤ F ⊔ (K ⊓ M)`; the reverse inclusion is immediate.
-/
import Mathlib
import Submission.Work.BSW.S3.S31setup

namespace Work.BSW.S3

open Subgroup Work.GW2

/-- In a finite group of odd order every element is a square: `x ↦ x * x` is injective because
there is no element of order `2`, hence bijective on a finite type. -/
theorem exists_sq_eq_of_odd_card {A : Type*} [Group A] [Finite A]
    (hodd : Odd (Nat.card A)) (y : A) : ∃ z : A, z * z = y := by
  have hcop : (Nat.card A).Coprime 2 := Nat.coprime_two_right.mpr hodd
  obtain ⟨z, hz⟩ := (Nat.Coprime.pow_left_bijective (G := A) hcop).2 y
  exact ⟨z, by simpa [pow_two] using hz⟩

/-- If `t * t = 1` and `t` inverts a subgroup `H ≤ G` (conjugation by `t` is inversion on `H`),
then `t * m * t * m⁻¹` centralizes `H` for every `m ∈ N_G(H)`: conjugation by `t * m * t` agrees
with conjugation by `m` on `H`. -/
theorem conj_tmt_mem_centralizer {A : Type} [Group A] {H : Subgroup A} {t m : A}
    (ht2 : t * t = 1) (ht : ∀ c ∈ H, t * c * t = c⁻¹)
    (hm : m ∈ Subgroup.normalizer (H : Set A)) :
    t * m * t * m⁻¹ ∈ Subgroup.centralizer (H : Set A) := by
  refine Subgroup.mem_centralizer_iff.mpr (fun c hc => ?_)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hm1 : m⁻¹ * c * m ∈ H := by
    simpa using
      ((Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (H : Set A)).inv_mem hm)) c).mp hc
  have hcong : t * (m⁻¹ * c * m) * t = (m⁻¹ * c * m)⁻¹ := ht _ hm1
  have hcong2 : t * c⁻¹ * t = c := by simpa using ht c⁻¹ (H.inv_mem hc)
  have hginv : (t * m * t * m⁻¹)⁻¹ = m * t * m⁻¹ * t := by
    rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, htinv]
    group
  have hkey : (t * m * t * m⁻¹) * c * (t * m * t * m⁻¹)⁻¹ = c := by
    rw [hginv]
    calc (t * m * t * m⁻¹) * c * (m * t * m⁻¹ * t)
        = t * (m * (t * (m⁻¹ * c * m) * t) * m⁻¹) * t := by group
      _ = t * (m * (m⁻¹ * c * m)⁻¹ * m⁻¹) * t := by rw [hcong]
      _ = t * c⁻¹ * t := by group
      _ = c := hcong2
  have hcomm : c * (t * m * t * m⁻¹) = (t * m * t * m⁻¹) * c := by
    have h1 := congrArg (fun z => z * (t * m * t * m⁻¹)) hkey
    simpa [mul_assoc] using h1.symm
  exact hcomm

/-- Bender §3.1 (ii): the normalizer of `F = C_G(x)` is `F` times the `F`-normalizer of `K`,
i.e. `N_G(C_G(x)) = C_G(x) ⊔ (K ⊓ N_G(C_G(x)))`. -/
theorem normalizerStruct {G : Type} [Group G] [Finite G] {t s x : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hx : x ∉ Work.BSW.HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊔
        (K ⊓ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)) := by
  refine le_antisymm ?_ (sup_le Subgroup.le_normalizer inf_le_right)
  intro m hm
  -- `c₀ = t * m * t * m⁻¹` centralizes `F`, hence lies in `F = C_G(F)`
  have hc0 : t * m * t * m⁻¹ ∈ Subgroup.centralizer ({x} : Set G) := by
    have h1 := conj_tmt_mem_centralizer (Work.BSW.t_mul_self h)
      (inverts_centralizer h hx hinv) hm
    rwa [centralizer_centralizer_eq_self h hx hinv] at h1
  -- `m⁻¹ * c₀ * m ∈ F`, since `m ∈ N_G(F)`
  have hmF : m⁻¹ * (t * m * t * m⁻¹) * m ∈ Subgroup.centralizer ({x} : Set G) := by
    simpa using
      ((Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)).inv_mem hm))
        (t * m * t * m⁻¹)).mp hc0
  -- `|F|` is odd, so we may take a square root of `m⁻¹ * c₀ * m` inside `F`
  obtain ⟨f, hfF, hff⟩ : ∃ f : G, f ∈ Subgroup.centralizer ({x} : Set G) ∧
      f * f = m⁻¹ * (t * m * t * m⁻¹) * m := by
    obtain ⟨z, hz⟩ := exists_sq_eq_of_odd_card (A := ↥(Subgroup.centralizer ({x} : Set G)))
      (odd_card_centralizer_of_notMem_HG h hx) ⟨m⁻¹ * (t * m * t * m⁻¹) * m, hmF⟩
    exact ⟨z, z.2, by simpa using congrArg Subtype.val hz⟩
  -- `m * f` is centralized by `t`
  have hcond : t * (m * f) * t = m * f := by
    have hft : t * f * t = f⁻¹ := inverts_centralizer h hx hinv f hfF
    have hc0m : t * m * t = (t * m * t * m⁻¹) * m := by group
    have hA : (t * m * t) * (t * f * t) = t * (m * f) * t := by
      rw [show (t * m * t) * (t * f * t) = t * m * (t * t) * f * t by group,
        Work.BSW.t_mul_self h]
      group
    have hstep1 : (t * m * t) * (t * f * t) = ((t * m * t * m⁻¹) * m) * f⁻¹ := by
      conv_lhs => rw [hc0m]
      rw [hft]
    calc t * (m * f) * t = (t * m * t) * (t * f * t) := hA.symm
      _ = ((t * m * t * m⁻¹) * m) * f⁻¹ := hstep1
      _ = (m * (m⁻¹ * (t * m * t * m⁻¹) * m)) * f⁻¹ := by group
      _ = (m * (f * f)) * f⁻¹ := by rw [← hff]
      _ = m * f := by group
  have hmfC : m * f ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcond' : t * (m * f) * t⁻¹ = m * f := by
      rw [Work.BSW.t_inv h]
      exact hcond
    exact (mul_inv_eq_iff_eq_mul.mp hcond').symm
  have hmfM : m * f ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) :=
    Subgroup.mul_mem _ hm ((Subgroup.centralizer ({x} : Set G)).le_normalizer hfF)
  have hmfK : m * f ∈ K := by
    have h1 : m * f ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) ⊓ K := by
      rw [← inf_normalizer_centralizer_t_eq_inf_K h hx hinv]
      exact ⟨hmfM, hmfC⟩
    exact h1.2
  rw [show m = (m * f) * f⁻¹ by group]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_right
      (show m * f ∈ K ⊓ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G)
        from ⟨hmfK, hmfM⟩))
    (Subgroup.mem_sup_left ((Subgroup.centralizer ({x} : Set G)).inv_mem hfF))

end Work.BSW.S3
