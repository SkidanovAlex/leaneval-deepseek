import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.sigmaAQ_petal_sum_ne_zero

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# (A3)(iii) Petal non-vanishing for the *strata* `Σ_A` in `ZMod Q_S`

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4
(Lemma `ortho`(iii) and the proof of Theorem `ortho-apply`), in the finite-group formulation of
`ZModArcs.lean`.

For a finite set `S` of pairwise coprime integers `≥ 2`, the points of the stratum `Σ_A`
(`= sigmaStrataQ (QA S) A`, the points of the torsion subgroup `𝕋[Q_A]` that do not lie in any
smaller subgroup `𝕋[Q_B]`, `B ⊊ A`) lift to the cyclic group `ZMod (QA S)`; this is the version of
Tao's arc system that makes the strata a partition of `Σ_{≤k}` (see the discussion of
`sigmaStrataQ` in `ZModArcs.lean`).  In contrast to `sigmaAQ`, a point of `sigmaStrataQ (QA S) A`
need *not* have exact denominator `Q_A`; all that is used below is that it lies in the torsion
subgroup `sigmaSubAQ (QA S) A = 𝕋[Q_A]`.

This file proves the numerator orthogonality of Tao's `ortho`(iii) for the strata: for pairwise
**disjoint** petals `P i ⊆ S` and a core `A₀ ⊆ S` disjoint from all of them,

`Σ_i (α_i + γ_i) − Σ_i (β_i + δ_i) ≠ 0`   in `ZMod (QA S)`

whenever `α_i, β_i ∈ Σ_{P_i}`, `γ_i, δ_i ∈ Σ_{A₀}`, and `α_i ≠ β_i` for at least one `i`.

The proof is the standard "kill everything else" argument, followed here by an *injectivity* step
rather than a non-vanishing step.  Let `j` be a coordinate with `α_j ≠ β_j` and put
`k = Q_{S ∖ P_j}`.  Since `P i ⊆ S ∖ P j` for `i ≠ j`, and `A₀ ⊆ S ∖ P j` by disjointness, the
multiplication by `k` kills every term of the identity except the `j`-th petal difference: each
term lies in a torsion subgroup `𝕋[Q_C]` with `Q_C ∣ k`.  What survives is

`k • α_j = k • β_j`   in `𝕋[Q_{P_j}]`,

and multiplication by `k` is **injective** on `𝕋[Q_{P_j}]` because `k` is coprime to `Q_{P_j}`
(the petals are disjoint); so `α_j = β_j`, a contradiction.  This is exactly where the strata
version is *easier* than `sigmaAQ_petal_sum_ne_zero`, whose final step needs `α_j` to have exact
denominator `Q_{P_j}`: here only `α_j ≠ β_j` inside the torsion subgroup is needed.
-/

open Finset
open scoped BigOperators

namespace Work.BourgainPlan.IonescuWainger

/-- **The elements of `sigmaSubAQ Q A`**: the lifts `a·(Q/Q_A)` of the numerators `a < Q_A`. -/
lemma mem_sigmaSubAQ_iff_petal {Q : ℕ} (x : ZMod Q) (A : Finset ℕ) :
    x ∈ sigmaSubAQ Q A ↔ ∃ a : ℕ, a < QA A ∧ x = arcLift Q A (a : ℤ) := by
  rw [sigmaSubAQ, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, Finset.mem_range.mp ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, Finset.mem_range.mpr ha, rfl⟩

/-- The arc point `c/Q_A` lies in the torsion subgroup `Σ_{⊆ A} = 𝕋[Q_A]`. -/
lemma arcPt_mem_sigmaSubA (A : Finset ℕ) (c : ℤ) : arcPt (QA A) c ∈ sigmaSubA A := ⟨c, rfl⟩

/-- **A unit of `Q_A` acts injectively on the torsion subgroup `Σ_{⊆ A} = 𝕋[Q_A]`**: if
`k` is coprime to `Q_A` and `x, y ∈ Σ_{⊆ A}` are distinct, then `k • x ≠ k • y`.  (Both points are
`c/Q_A`; multiplying by `k` shifts the numerators by a unit modulo `Q_A`.) -/
lemma zsmul_ne_of_ne_of_mem_sigmaSubA {A : Finset ℕ} (hA : ∀ q ∈ A, q ≠ 0) {k : ℕ}
    (hcop : Nat.Coprime k (QA A)) {x y : Circle} (hx : x ∈ sigmaSubA A) (hy : y ∈ sigmaSubA A)
    (hxy : x ≠ y) : (k : ℤ) • x ≠ (k : ℤ) • y := by
  obtain ⟨c, rfl⟩ := hx
  obtain ⟨c', rfl⟩ := hy
  exact zsmul_arcPt_ne_of_ne (N := (k : ℤ)) (Q := QA A) (QA_ne_zero hA)
    (by simpa using hcop) hxy

/-- **Petal non-vanishing for the strata in `ZMod (QA S)`** (Tao's `ortho`(iii), arithmetic core,
strata version).  Let `S` be a finite set of pairwise coprime integers `≥ 2`, let
`P : Fin r → Finset ℕ` be pairwise disjoint subsets of `S` (the petals) and let `A₀ ⊆ S` be
disjoint from every petal.  If `α i, β i` lie in the stratum `Σ_{P i}` and differ in at least one
coordinate, while `γ i, δ i` lie in the stratum `Σ_{A₀}`, then

`Σ_i (α i + γ i) - Σ_i (β i + δ i) ≠ 0`   in `ZMod (QA S)`. -/
theorem sigmaStrataQ_petal_sum_ne_zero {r : ℕ} {S : Finset ℕ} [NeZero (QA S)]
    (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A₀ : Finset ℕ} (hA₀ : A₀ ⊆ S)
    {P : Fin r → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisj : ∀ i j : Fin r, i ≠ j → Disjoint (P i) (P j))
    (hdisj₀ : ∀ i, Disjoint A₀ (P i))
    {α β : Fin r → ZMod (QA S)}
    (hα : ∀ i, α i ∈ sigmaStrataQ (QA S) (P i))
    (hβ : ∀ i, β i ∈ sigmaStrataQ (QA S) (P i))
    (hne : ∃ i, α i ≠ β i)
    (γ δ : Fin r → ZMod (QA S)) (hγ : ∀ i, γ i ∈ sigmaStrataQ (QA S) A₀)
    (hδ : ∀ i, δ i ∈ sigmaStrataQ (QA S) A₀) :
    (∑ i, (α i + γ i)) - (∑ i, (β i + δ i)) ≠ 0 := by
  classical
  intro htotal
  obtain ⟨j, hj⟩ := hne
  -- every stratum is contained in the corresponding torsion subgroup
  have hαsub : ∀ i, α i ∈ sigmaSubAQ (QA S) (P i) := fun i => (Finset.mem_filter.mp (hα i)).1
  have hβsub : ∀ i, β i ∈ sigmaSubAQ (QA S) (P i) := fun i => (Finset.mem_filter.mp (hβ i)).1
  have hγsub : ∀ i, γ i ∈ sigmaSubAQ (QA S) A₀ := fun i => (Finset.mem_filter.mp (hγ i)).1
  have hδsub : ∀ i, δ i ∈ sigmaSubAQ (QA S) A₀ := fun i => (Finset.mem_filter.mp (hδ i)).1
  -- denominators of the arc points
  choose a _ ha_eq using fun i => (mem_sigmaSubAQ_iff_petal (α i) (P i)).mp (hαsub i)
  choose b _ hb_eq using fun i => (mem_sigmaSubAQ_iff_petal (β i) (P i)).mp (hβsub i)
  choose c _ hc_eq using fun i => (mem_sigmaSubAQ_iff_petal (γ i) A₀).mp (hγsub i)
  choose d _ hd_eq using fun i => (mem_sigmaSubAQ_iff_petal (δ i) A₀).mp (hδsub i)
  -- the corresponding points of the circle
  let Ac : Fin r → Circle := fun i => arcPt (QA (P i)) (a i : ℤ)
  let Bc : Fin r → Circle := fun i => arcPt (QA (P i)) (b i : ℤ)
  let Cc : Fin r → Circle := fun i => arcPt (QA A₀) (c i : ℤ)
  let Dc : Fin r → Circle := fun i => arcPt (QA A₀) (d i : ℤ)
  have hAc : ∀ i, ZMod.toAddCircle (α i) = Ac i := fun i => by
    rw [ha_eq i]
    exact toAddCircle_arcLift_petal (hP i) (a i : ℤ)
  have hBc : ∀ i, ZMod.toAddCircle (β i) = Bc i := fun i => by
    rw [hb_eq i]
    exact toAddCircle_arcLift_petal (hP i) (b i : ℤ)
  have hCc : ∀ i, ZMod.toAddCircle (γ i) = Cc i := fun i => by
    rw [hc_eq i]
    exact toAddCircle_arcLift_petal hA₀ (c i : ℤ)
  have hDc : ∀ i, ZMod.toAddCircle (δ i) = Dc i := fun i => by
    rw [hd_eq i]
    exact toAddCircle_arcLift_petal hA₀ (d i : ℤ)
  -- the vanishing identity, pushed to the circle
  have himg : ZMod.toAddCircle ((∑ i, (α i + γ i)) - (∑ i, (β i + δ i))) = 0 := by
    rw [htotal, map_zero]
  have hcirc : (∑ i, (Ac i + Cc i)) - (∑ i, (Bc i + Dc i)) = 0 := by
    rw [← himg]
    simp only [map_sub, map_sum, map_add, hAc, hBc, hCc, hDc]
  -- the multiplier `k = Q_{S ∖ P j}` kills every term but the `j`-th one
  have hsub_i : ∀ i : Fin r, i ≠ j → P i ⊆ S \ P j := fun i hij x hx =>
    Finset.mem_sdiff.mpr
      ⟨hP i hx, fun hxj => (Finset.disjoint_left.mp (hdisj i j hij) hx) hxj⟩
  have hsub₀ : A₀ ⊆ S \ P j := fun x hx =>
    Finset.mem_sdiff.mpr
      ⟨hA₀ hx, fun hxj => (Finset.disjoint_left.mp (hdisj₀ j) hx) hxj⟩
  have hdvd_i : ∀ i : Fin r, i ≠ j → QA (P i) ∣ QA (S \ P j) := fun i hij =>
    QA_dvd_of_subset (hsub_i i hij)
  have hdvd₀ : QA A₀ ∣ QA (S \ P j) := QA_dvd_of_subset hsub₀
  have hkillA : ∀ i : Fin r, i ≠ j → (QA (S \ P j) : ℤ) • Ac i = 0 := fun i hij =>
    zsmul_eq_zero_of_dvd_QA (fun q hq => by have := h2 q (hP i hq); omega) (hdvd_i i hij)
      (arcPt_mem_sigmaSubA (P i) (a i : ℤ))
  have hkillB : ∀ i : Fin r, i ≠ j → (QA (S \ P j) : ℤ) • Bc i = 0 := fun i hij =>
    zsmul_eq_zero_of_dvd_QA (fun q hq => by have := h2 q (hP i hq); omega) (hdvd_i i hij)
      (arcPt_mem_sigmaSubA (P i) (b i : ℤ))
  have hkillC : ∀ i, (QA (S \ P j) : ℤ) • Cc i = 0 := fun i =>
    zsmul_eq_zero_of_dvd_QA (fun q hq => by have := h2 q (hA₀ hq); omega) hdvd₀
      (arcPt_mem_sigmaSubA A₀ (c i : ℤ))
  have hkillD : ∀ i, (QA (S \ P j) : ℤ) • Dc i = 0 := fun i =>
    zsmul_eq_zero_of_dvd_QA (fun q hq => by have := h2 q (hA₀ hq); omega) hdvd₀
      (arcPt_mem_sigmaSubA A₀ (d i : ℤ))
  have h1 : (QA (S \ P j) : ℤ) • ((∑ i, (Ac i + Cc i)) - (∑ i, (Bc i + Dc i))) = 0 := by
    rw [hcirc, smul_zero]
  rw [smul_sub, Finset.smul_sum, Finset.smul_sum] at h1
  have hsumA : (∑ i, (QA (S \ P j) : ℤ) • (Ac i + Cc i)) = (QA (S \ P j) : ℤ) • Ac j := by
    have h := Finset.sum_eq_single (s := (Finset.univ : Finset (Fin r)))
      (f := fun i : Fin r => (QA (S \ P j) : ℤ) • (Ac i + Cc i)) j
      (fun i _ hij => by rw [smul_add, hkillA i hij, hkillC i, add_zero])
      (fun hj => absurd (Finset.mem_univ j) hj)
    rw [h, smul_add, hkillC j, add_zero]
  have hsumB : (∑ i, (QA (S \ P j) : ℤ) • (Bc i + Dc i)) = (QA (S \ P j) : ℤ) • Bc j := by
    have h := Finset.sum_eq_single (s := (Finset.univ : Finset (Fin r)))
      (f := fun i : Fin r => (QA (S \ P j) : ℤ) • (Bc i + Dc i)) j
      (fun i _ hij => by rw [smul_add, hkillB i hij, hkillD i, add_zero])
      (fun hj => absurd (Finset.mem_univ j) hj)
    rw [h, smul_add, hkillD j, add_zero]
  rw [hsumA, hsumB] at h1
  -- so `k • α_j = k • β_j`, but `k` is a unit modulo `Q_{P j}` and `α_j ≠ β_j`
  have hne_pt : arcPt (QA (P j)) (a j : ℤ) ≠ arcPt (QA (P j)) (b j : ℤ) := by
    intro hpt
    refine hj ?_
    have htc : ZMod.toAddCircle (α j) = ZMod.toAddCircle (β j) := by
      rw [hAc j, hBc j]
      exact hpt
    exact ZMod.toAddCircle_injective (QA S) htc
  have hdisjK : Disjoint (S \ P j) (P j) :=
    Finset.disjoint_left.mpr fun x hx hx' => (Finset.mem_sdiff.mp hx).2 hx'
  have hcop : Nat.Coprime (QA (S \ P j)) (QA (P j)) :=
    coprime_QA_of_disjoint_subset hS Finset.sdiff_subset (hP j) hdisjK
  have hQj : QA (P j) ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hP j hq)
  refine (zsmul_arcPt_ne_of_ne (N := (QA (S \ P j) : ℤ)) (Q := QA (P j)) hQj ?_ hne_pt) ?_
  · simpa using hcop
  · exact sub_eq_zero.mp h1

end Work.BourgainPlan.IonescuWainger
