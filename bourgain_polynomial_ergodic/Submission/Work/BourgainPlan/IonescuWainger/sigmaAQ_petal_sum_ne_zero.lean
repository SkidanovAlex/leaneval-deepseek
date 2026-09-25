import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ZModArcs
import Submission.Work.BourgainPlan.IonescuWainger.ArcCRT
import Submission.Work.BourgainPlan.IonescuWainger.ArcNumOrth

/-!
# (A3)(iii) Petal non-vanishing in the finite cyclic group `ZMod Q_S`

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4
(Lemma `ortho`(iii) and the proof of Theorem `ortho-apply`), in the finite-group formulation of
`ZModArcs.lean`.

For a finite set `S` of pairwise coprime integers `≥ 2`, the points of the arc `Σ_A` (`= sigmaA A`)
lift to the elements `arcLift (QA S) A a = a · (Q_S/Q_A)` of the cyclic group `ZMod (QA S)`, and
`sigmaAQ (QA S) A` is the corresponding finite set (Tao's `Σ_A` transported to `ZMod Q_S`).

This file proves the arithmetic core of Tao's *numerator* orthogonality in that vocabulary: for
pairwise **disjoint** petals `P i ⊆ S` and a core `A₀ ⊆ S` disjoint from all of them,

`Σ_i (α_i + γ_i) − Σ_i (β_i + δ_i) ≠ 0`   in `ZMod (QA S)`

whenever `α_i, β_i ∈ Σ_{P_i}`, `γ_i, δ_i ∈ Σ_{A₀}`, and `α_i ≠ β_i` for at least one `i`.

The proof is the standard "kill everything else" argument: let `k = Q_{S ∖ P_j}` be the product of
the primes *outside* the petal of a coordinate `j` with `α_j ≠ β_j`.  Passing to the circle `𝕋`
through the (additive) isomorphism `ZMod Q_S → 𝕋`, `x ↦ x/Q_S`, the identity becomes an identity in
`𝕋`; multiplying it by `k` kills every term — each of them lies in the torsion subgroup
`Σ_{⊆ C} = 𝕋[Q_C]` of a set `C` disjoint from `P j`, so that `Q_C ∣ k` — except the `j`-th petal
difference, which is a point of *exact* denominator `Q_{P_j}`, hence stays non-zero after
multiplication by a `k` coprime to `Q_{P_j}`.  That contradicts the vanishing.

The ingredients already in the repository are the circle-side lemmas `zsmul_eq_zero_of_dvd_QA`,
`sigmaA_subset_sigmaSubA` (`ArcCRT.lean`), `arcPt_sub_same`, `zsmul_arcPt_ne_zero_of_coprime_nat`
(`ArcNumOrth.lean`) and the lift–arc dictionary `arcLift_arcPt` (`ZModArcs.lean`); what is added
here is the transfer of the statement to the circle and the bookkeeping of the products
`Q_C ∣ Q_{S ∖ P_j}`.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-! ## The dictionary between `ZMod Q` and the circle -/

/-- **The elements of `sigmaAQ Q A`**: the lifts `a · (Q/Q_A)` of the points `a/Q_A` with
`gcd(a, Q_A) = 1`, `a < Q_A`. -/
lemma mem_sigmaAQ_iff {Q : ℕ} (x : ZMod Q) (A : Finset ℕ) :
    x ∈ sigmaAQ Q A ↔ ∃ a : ℕ, a < QA A ∧ Nat.Coprime a (QA A) ∧ x = arcLift Q A (a : ℤ) := by
  rw [sigmaAQ, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [Finset.mem_filter, Finset.mem_range] at ha
    exact ⟨a, ha.1, ha.2, rfl⟩
  · rintro ⟨a, ha, hcop, rfl⟩
    exact ⟨a, by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨ha, hcop⟩, rfl⟩

/-- The integer points of `ZMod Q` and the points `z/Q` of `𝕋` agree through `x ↦ x/Q`. -/
lemma arcPt_eq_toAddCircle {Q : ℕ} [NeZero Q] (z : ℤ) :
    arcPt Q z = ZMod.toAddCircle ((z : ℤ) : ZMod Q) := by
  rw [arcPt, ZMod.toAddCircle_intCast]

/-- **The lift of an arc point is that arc point**: the image of `arcLift (QA S) A z` under the
isomorphism `ZMod (QA S) ≅ 𝕋` is `z/Q_A`. -/
lemma toAddCircle_arcLift_petal {S : Finset ℕ} [NeZero (QA S)] {A : Finset ℕ} (hA : A ⊆ S) (z : ℤ) :
    ZMod.toAddCircle (arcLift (QA S) A z) = arcPt (QA A) z := by
  have hdvd : QA A ∣ QA S := Finset.prod_dvd_prod_of_subset A S (fun x => x) hA
  rw [arcLift, ← Int.cast_mul, ← arcPt_eq_toAddCircle]
  exact arcLift_arcPt hdvd (NeZero.ne (QA S)) z

/-! ## Products `Q_A` for subsets of `S` -/

/-- `Q_A ∣ Q_B` when `A ⊆ B`. -/
lemma QA_dvd_of_subset {A B : Finset ℕ} (h : A ⊆ B) : QA A ∣ QA B :=
  Finset.prod_dvd_prod_of_subset A B (fun x => x) h

/-- **`Q_A` and `Q_B` are coprime for disjoint `A, B ⊆ S`**, `S` being pairwise coprime. -/
lemma coprime_QA_of_disjoint_subset {S A B : Finset ℕ}
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA : A ⊆ S) (hB : B ⊆ S) (hdisj : Disjoint A B) : Nat.Coprime (QA A) (QA B) :=
  Nat.Coprime.prod_left fun q hq =>
    Nat.Coprime.prod_right fun q' hq' =>
      hS q (hA hq) q' (hB hq') (fun he => (Finset.disjoint_left.mp hdisj hq) (he ▸ hq'))

/-! ## The main lemma -/

/-- **Petal non-vanishing in `ZMod (QA S)`** (Tao's `ortho`(iii), arithmetic core).  Let `S` be a
finite set of pairwise coprime integers `≥ 2`, let `P : Fin r → Finset ℕ` be pairwise disjoint
subsets of `S` (the petals) and let `A₀ ⊆ S` be disjoint from every petal.  If
`α i, β i ∈ sigmaAQ (QA S) (P i)` differ in at least one coordinate and `γ i, δ i` lie in
`sigmaAQ (QA S) A₀`, then
`Σ_i (α i + γ i) - Σ_i (β i + δ i) ≠ 0`. -/
theorem sigmaAQ_petal_sum_ne_zero {r : ℕ} {S : Finset ℕ} [NeZero (QA S)]
    (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A₀ : Finset ℕ} (hA₀ : A₀ ⊆ S)
    {P : Fin r → Finset ℕ} (hP : ∀ i, P i ⊆ S)
    (hdisj : ∀ i j : Fin r, i ≠ j → Disjoint (P i) (P j))
    (hdisj₀ : ∀ i, Disjoint A₀ (P i))
    {α β : Fin r → ZMod (QA S)}
    (hα : ∀ i, α i ∈ sigmaAQ (QA S) (P i)) (hβ : ∀ i, β i ∈ sigmaAQ (QA S) (P i))
    (hne : ∃ i, α i ≠ β i)
    (γ δ : Fin r → ZMod (QA S)) (hγ : ∀ i, γ i ∈ sigmaAQ (QA S) A₀)
    (hδ : ∀ i, δ i ∈ sigmaAQ (QA S) A₀) :
    (∑ i, (α i + γ i)) - (∑ i, (β i + δ i)) ≠ 0 := by
  classical
  intro htotal
  obtain ⟨j, hne0⟩ := hne
  -- `P j` is non-empty, so that `Q_{P j} ≠ 0`
  have hPj_ne : P j ≠ ∅ := by
    intro hemp
    apply hne0
    have hzero : ∀ x ∈ sigmaAQ (QA S) (P j), x = 0 := by
      intro x hx
      obtain ⟨n, -, -, rfl⟩ := (mem_sigmaAQ_iff x (P j)).mp hx
      rw [hemp, arcLift, show QA (∅ : Finset ℕ) = 1 from rfl, Nat.div_one]
      simp
    rw [hzero (α j) (hα j), hzero (β j) (hβ j)]
  have hQj : QA (P j) ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hP j hq)
  -- representations of the four families of arc points
  choose a ha_lt ha_cop ha_eq using fun i => (mem_sigmaAQ_iff (α i) (P i)).mp (hα i)
  choose b hb_lt hb_cop hb_eq using fun i => (mem_sigmaAQ_iff (β i) (P i)).mp (hβ i)
  choose c hc_lt hc_cop hc_eq using fun i => (mem_sigmaAQ_iff (γ i) A₀).mp (hγ i)
  choose d hd_lt hd_cop hd_eq using fun i => (mem_sigmaAQ_iff (δ i) A₀).mp (hδ i)
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
  -- all four families lie in the appropriate torsion subgroup
  have hAcA : ∀ i, Ac i ∈ sigmaSubA (P i) := fun i =>
    sigmaA_subset_sigmaSubA (P i) ⟨(a i : ℤ), by simpa using ha_cop i, rfl⟩
  have hBcA : ∀ i, Bc i ∈ sigmaSubA (P i) := fun i =>
    sigmaA_subset_sigmaSubA (P i) ⟨(b i : ℤ), by simpa using hb_cop i, rfl⟩
  have hCcA : ∀ i, Cc i ∈ sigmaSubA A₀ := fun i =>
    sigmaA_subset_sigmaSubA A₀ ⟨(c i : ℤ), by simpa using hc_cop i, rfl⟩
  have hDcA : ∀ i, Dc i ∈ sigmaSubA A₀ := fun i =>
    sigmaA_subset_sigmaSubA A₀ ⟨(d i : ℤ), by simpa using hd_cop i, rfl⟩
  have hkillA : ∀ i : Fin r, i ≠ j → (QA (S \ P j) : ℤ) • Ac i = 0 := fun i hij =>
    zsmul_eq_zero_of_dvd_QA (fun q hq => by have := h2 q (hP i hq); omega)
      (hdvd_i i hij) (hAcA i)
  have hkillB : ∀ i : Fin r, i ≠ j → (QA (S \ P j) : ℤ) • Bc i = 0 := fun i hij =>
    zsmul_eq_zero_of_dvd_QA (fun q hq => by have := h2 q (hP i hq); omega)
      (hdvd_i i hij) (hBcA i)
  have hkillC : ∀ i, (QA (S \ P j) : ℤ) • Cc i = 0 := fun i =>
    zsmul_eq_zero_of_dvd_QA (fun q hq => by have := h2 q (hA₀ hq); omega) hdvd₀ (hCcA i)
  have hkillD : ∀ i, (QA (S \ P j) : ℤ) • Dc i = 0 := fun i =>
    zsmul_eq_zero_of_dvd_QA (fun q hq => by have := h2 q (hA₀ hq); omega) hdvd₀ (hDcA i)
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
  have hAj : (QA (S \ P j) : ℤ) • (Ac j - Bc j) = 0 := by
    rw [smul_sub]
    exact h1
  -- but the `j`-th petal difference survives
  have hne_pt : arcPt (QA (P j)) (a j : ℤ) ≠ arcPt (QA (P j)) (b j : ℤ) := by
    intro hpt
    refine hne0 ?_
    have h2' : ZMod.toAddCircle (α j) = ZMod.toAddCircle (β j) := by
      rw [hAc j, hBc j]
      simpa only [Ac, Bc] using hpt
    exact ZMod.toAddCircle_injective (QA S) h2'
  have hpt0 : arcPt (QA (P j)) ((a j : ℤ) - (b j : ℤ)) ≠ 0 := by
    have h := sub_ne_zero.mpr hne_pt
    rwa [arcPt_sub_same] at h
  have hdisjK : Disjoint (S \ P j) (P j) :=
    Finset.disjoint_left.mpr fun x hx hx' => (Finset.mem_sdiff.mp hx).2 hx'
  have hcop : Nat.Coprime (QA (S \ P j)) (QA (P j)) :=
    coprime_QA_of_disjoint_subset hS Finset.sdiff_subset (hP j) hdisjK
  exact (zsmul_arcPt_ne_zero_of_coprime_nat hQj hcop hpt0)
    (by simpa only [Ac, Bc, arcPt_sub_same] using hAj)

end Work.BourgainPlan.IonescuWainger
