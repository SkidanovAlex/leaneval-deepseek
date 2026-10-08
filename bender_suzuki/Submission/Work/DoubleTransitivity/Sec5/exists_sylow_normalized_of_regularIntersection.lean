import Mathlib
import Submission.Work.DoubleTransitivity.Sec2.prop2
import Submission.Work.DoubleTransitivity.Sec4.Defs
import Submission.Work.DoubleTransitivity.App2.app2_5

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec5.exists_sylow_normalized_of_regularIntersection`

Peterfalvi, *Le théorème de Bender–Suzuki I*, Ch. I §4 Lemma 1, the direction
(c) ⟹ "`D` has a `p`-Sylow normalised by any given `u ∈ Inv(H)`".

Let `H` be a Bender subgroup of the finite group `G`, `t ∉ H` an involution, so that
`D = H ∩ H^t = twoPoint H t` and, by §2 Prop. 2 (b), `D` acts transitively on `Inv(H)`.
Assume `D` is a `p`-regular intersection relative to `H`, i.e. (definition of
`IsRegularIntersection`) some `p`-Sylow `P₀` of `D` has `|N_H(P₀)|` even.  Then for *every*
involution `u ∈ H` there is a `p`-Sylow `P` of `D` with `u ∈ N_G(P)`.

Proof.  `|N_H(P₀)|` even gives, by Cauchy, an involution `u₀ ∈ N_H(P₀)` normalising `P₀`.
Since `D` is transitive on `Inv(H)`, there is `d ∈ D` with `d⁻¹ u d = u₀`.  Then
`P := d P₀ d⁻¹ = conj d P₀` is a `p`-Sylow of `conj d D = D` (conjugation carries Sylows to
Sylows), and `u = d u₀ d⁻¹` normalises `P` because `u₀` normalises `P₀`. -/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.DoubleTransitivity.Sec5

open Submission.Blueprint

theorem exists_sylow_normalized_of_regularIntersection {G : Type} [Group G] [Finite G]
    {H : Subgroup G} (hH : Work.DoubleTransitivity.IsBender H) (hne : H ≠ ⊤)
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    {p : ℕ} (hreg : Work.DoubleTransitivity.IsRegularIntersection p
        (Submission.Blueprint.twoPoint H t) H)
    {u : G} (hu : u ∈ Submission.Blueprint.involutions (H : Set G)) :
    ∃ P : Subgroup G, Work.DoubleTransitivity.IsSylowSubgroupOf p P
        (Submission.Blueprint.twoPoint H t) ∧
      u ∈ Subgroup.normalizer (P : Set G) := by
  classical
  -- Unfold the regular-intersection hypothesis: a `p`-Sylow `P₀` of `D = H ∩ H^t` whose
  -- `H`-normaliser has even order.
  obtain ⟨P₀, hP₀, heven⟩ := hreg
  -- Cauchy: `|N_H(P₀)|` even produces an involution `u₀ ∈ N_H(P₀)`.
  have h2dvd : 2 ∣ Nat.card ↥(Subgroup.normalizer (P₀ : Set G) ⊓ H) :=
    even_iff_two_dvd.mp heven
  obtain ⟨u₀, hu₀ord⟩ := exists_prime_orderOf_dvd_card' 2
    (G := ↥(Subgroup.normalizer (P₀ : Set G) ⊓ H)) h2dvd
  have hu₀memN : (u₀ : G) ∈ Subgroup.normalizer (P₀ : Set G) ⊓ H := u₀.2
  have hu₀norm : (u₀ : G) ∈ Subgroup.normalizer (P₀ : Set G) :=
    (Subgroup.mem_inf.mp hu₀memN).1
  have hu₀H : (u₀ : G) ∈ H := (Subgroup.mem_inf.mp hu₀memN).2
  have hu₀ordG : orderOf (u₀ : G) = 2 := by rw [Subgroup.orderOf_coe, hu₀ord]
  have hu₀inv : (u₀ : G) ∈ Submission.Blueprint.involutions (H : Set G) :=
    ⟨hu₀H, hu₀ordG⟩
  -- `u₀` normalises `P₀`.
  have hu₀conj : Submission.Blueprint.conj (u₀ : G) P₀ = P₀ :=
    (conj_eq_self_iff_mem_normalizer (u₀ : G) P₀).mpr hu₀norm
  -- §2 Prop. 2 (b): `D` is transitive on the involutions of `H`.
  obtain ⟨htrans, -, -⟩ := Work.DoubleTransitivity.Sec2.prop2 hH hne ht htH
  obtain ⟨d, hdD, hdu⟩ := htrans u (u₀ : G) hu hu₀inv
  -- `P := d P₀ d⁻¹` is a `p`-Sylow of `conj d D = D`.
  have hDconj : Submission.Blueprint.conj d (Submission.Blueprint.twoPoint H t) =
      Submission.Blueprint.twoPoint H t :=
    (conj_eq_self_iff_mem_normalizer d _).mpr (Subgroup.le_normalizer hdD)
  have hPsyl : Work.DoubleTransitivity.IsSylowSubgroupOf p
      (Submission.Blueprint.conj d P₀) (Submission.Blueprint.twoPoint H t) := by
    have h := Work.DoubleTransitivity.App2.isSylowSubgroupOf_conj hP₀ d
    rwa [hDconj] at h
  refine ⟨Submission.Blueprint.conj d P₀, hPsyl, ?_⟩
  -- `u = d u₀ d⁻¹` normalises `d P₀ d⁻¹` because `u₀` normalises `P₀`.
  have hud : u * d = d * (u₀ : G) := by
    calc u * d = d * (d⁻¹ * u * d) := by group
      _ = d * (u₀ : G) := by rw [hdu]
  refine (conj_eq_self_iff_mem_normalizer u (Submission.Blueprint.conj d P₀)).mp ?_
  rw [← conj_mul, hud, conj_mul, hu₀conj]

end Work.DoubleTransitivity.Sec5
