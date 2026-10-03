import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ArcFinsetDefs
import Submission.Work.BourgainPlan.IonescuWainger.ArcNumOrth

open Work.BourgainPlan.IonescuWainger (arcPt QA sigmaSubAFinset sigmaSubA)
namespace Work.IonescuWainger

open Work.BourgainPlan.IonescuWainger (coprime_QA_of_disjoint sigmaSubA_zsmul_eq_zero arcPt_sub_denom zsmul_arcPt' arcPt_eq_zero_iff_dvd QA_ne_zero_of_two_le arcPt_sub_same arcPt_add_denom QA_union sigmaLe_separation)

local notation "𝕋" => Work.BourgainPlan.IonescuWainger.Circle

/-- A `Finset`-indexed union of arcs around the shifted points `β + c` is closed: it is the
finite union of the closed balls `closedBall (β + c) ε`. -/
lemma isClosed_arcBall (F : Finset 𝕋) (c : 𝕋) (ε : ℝ) :
    IsClosed {ξ : 𝕋 | ∃ β ∈ F, ξ - (β + c) ∈ Metric.closedBall (0 : 𝕋) ε} := by
  have heq : {ξ : 𝕋 | ∃ β ∈ F, ξ - (β + c) ∈ Metric.closedBall (0 : 𝕋) ε}
      = ⋃ β ∈ (F : Set 𝕋), Metric.closedBall (β + c) ε := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Metric.mem_closedBall, Finset.mem_coe]
    constructor
    · rintro ⟨β, hβ, h⟩; exact ⟨β, hβ, by rw [dist_eq_norm]; simpa using h⟩
    · rintro ⟨β, hβ, h⟩; exact ⟨β, hβ, by rw [dist_eq_norm] at h; simpa using h⟩
  rw [heq]
  exact (F.finite_toSet).isClosed_biUnion fun β _ => Metric.isClosed_closedBall

/-- **The translated arc points are distinct.**  If `β, β' ∈ Σ_{⊆A₀}` and the arc points
`α = a/Q_D`, `α' = a'/Q_{D'}` differ (with `D, D' ⊆ S \ A₀` in a pairwise coprime `S`), then
`β + α ≠ β' + α'`: equality would give `α - α' = β' - β ∈ Σ_{⊆A₀}`, i.e. `Q_{A₀}·(α - α') = 0`,
and writing `α - α' = c/(Q_D Q_{D'})` the coprimality of `Q_D Q_{D'}` with `Q_{A₀}` forces
`Q_D Q_{D'} ∣ c`, i.e. `α = α'`. -/
lemma shift_ne_of_arcPt_ne {S A₀ D D' : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) (hA₀ : A₀ ⊆ S)
    (hD : D ⊆ S \ A₀) (hD' : D' ⊆ S \ A₀) {b b' a a' : ℤ}
    (hne : arcPt (QA D) a ≠ arcPt (QA D') a') :
    arcPt (QA A₀) b + arcPt (QA D) a ≠ arcPt (QA A₀) b' + arcPt (QA D') a' := by
  intro heq
  have hkey : arcPt (QA D) a - arcPt (QA D') a' = arcPt (QA A₀) (b' - b) := by
    have hstep : arcPt (QA D) a - arcPt (QA D') a' = arcPt (QA A₀) b' - arcPt (QA A₀) b := by
      rw [← sub_eq_zero]
      have : (arcPt (QA D) a - arcPt (QA D') a') - (arcPt (QA A₀) b' - arcPt (QA A₀) b)
          = (arcPt (QA A₀) b + arcPt (QA D) a) - (arcPt (QA A₀) b' + arcPt (QA D') a') := by
        abel
      rw [this, heq, sub_self]
    rw [hstep, ← arcPt_sub_same (QA A₀) b' b]
  have hmem : arcPt (QA D) a - arcPt (QA D') a' ∈ sigmaSubA A₀ := by
    rw [hkey]; exact ⟨b' - b, rfl⟩
  have hz := sigmaSubA_zsmul_eq_zero (A := A₀) (fun q hq => h2 q (hA₀ hq)) hmem
  have hQDne : QA D ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q ((Finset.mem_sdiff.mp (hD hq)).1)
  have hQD'ne : QA D' ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q ((Finset.mem_sdiff.mp (hD' hq)).1)
  have hsub := arcPt_sub_denom (Q := QA D) (R := QA D') hQDne hQD'ne a a'
  have hz' : arcPt (QA D * QA D') ((QA A₀ : ℤ) * (a * (QA D' : ℤ) - a' * (QA D : ℤ))) = 0 := by
    rw [hsub, zsmul_arcPt'] at hz
    exact hz
  have hQne : QA D * QA D' ≠ 0 := Nat.mul_ne_zero hQDne hQD'ne
  have hdvd : ((QA D * QA D' : ℕ) : ℤ) ∣ (QA A₀ : ℤ) * (a * (QA D' : ℤ) - a' * (QA D : ℤ)) :=
    (arcPt_eq_zero_iff_dvd hQne _).mp hz'
  have hcop : Nat.Coprime (QA D * QA D') (QA A₀) :=
    Nat.Coprime.mul_left
      (coprime_QA_of_disjoint fun q hq q' hq' => hS q ((Finset.mem_sdiff.mp (hD hq)).1) q' (hA₀ hq') (by
        intro h; exact (Finset.mem_sdiff.mp (hD hq)).2 (h ▸ hq')))
      (coprime_QA_of_disjoint fun q hq q' hq' => hS q ((Finset.mem_sdiff.mp (hD' hq)).1) q' (hA₀ hq') (by
        intro h; exact (Finset.mem_sdiff.mp (hD' hq)).2 (h ▸ hq')))
  have hdvd' : ((QA D * QA D' : ℕ) : ℤ) ∣ (a * (QA D' : ℤ) - a' * (QA D : ℤ)) :=
    (Nat.Coprime.isCoprime hcop).dvd_of_dvd_mul_left hdvd
  have hzero : arcPt (QA D * QA D') (a * (QA D' : ℤ) - a' * (QA D : ℤ)) = 0 :=
    (arcPt_eq_zero_iff_dvd hQne _).mpr hdvd'
  refine hne (sub_eq_zero.mp ?_)
  rw [hsub]; exact hzero

/-- **Tao's `ortho`(i) for the translated torsion arcs.**  The translated arc points
`β + a/Q_D`, `β' + a'/Q_{D'}` lie in `Σ_{≤ k}` (they have denominator dividing
`Q_{A₀ ∪ D}`, `Q_{A₀ ∪ D'}` with `|A₀ ∪ D|, |A₀ ∪ D'| ≤ k`), and are distinct by
`shift_ne_of_arcPt_ne`; hence they are `1/qmax^{2k}`-separated by `sigmaLe_separation`. -/
lemma shiftArc_separation {S A₀ D D' : Finset ℕ} {k qmax : ℕ} {a a' : ℤ}
    (h2 : ∀ q ∈ S, 2 ≤ q) (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    (hA₀ : A₀ ⊆ S) (hk₀ : A₀.card ≤ k)
    (hD : D ⊆ S \ A₀) (hD' : D' ⊆ S \ A₀) (hDk : D.card ≤ k - A₀.card)
    (hD'k : D'.card ≤ k - A₀.card)
    (hmax : ∀ q ∈ S, q ≤ qmax) (hne : arcPt (QA D) a ≠ arcPt (QA D') a')
    {β β' : 𝕋} (hβ : β ∈ sigmaSubAFinset A₀) (hβ' : β' ∈ sigmaSubAFinset A₀) :
    1 / (qmax : ℝ) ^ (2 * k) ≤ ‖(β + arcPt (QA D) a) - (β' + arcPt (QA D') a')‖ := by
  obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hβ
  obtain ⟨b', -, hb'⟩ := Finset.mem_image.mp hβ'
  rw [← hb, ← hb']
  have hAdisj : Disjoint A₀ D := by
    rw [Finset.disjoint_left]
    intro q hq hqD
    exact (Finset.mem_sdiff.mp (hD hqD)).2 hq
  have hAdisj' : Disjoint A₀ D' := by
    rw [Finset.disjoint_left]
    intro q hq hqD
    exact (Finset.mem_sdiff.mp (hD' hqD)).2 hq
  have hDsub : D ⊆ S := fun q hq => (Finset.mem_sdiff.mp (hD hq)).1
  have hD'sub : D' ⊆ S := fun q hq => (Finset.mem_sdiff.mp (hD' hq)).1
  have hAsub : A₀ ∪ D ⊆ S := Finset.union_subset hA₀ hDsub
  have hA'sub : A₀ ∪ D' ⊆ S := Finset.union_subset hA₀ hD'sub
  have hAcard : (A₀ ∪ D).card ≤ k := by
    rw [Finset.card_union_of_disjoint hAdisj]; omega
  have hA'card : (A₀ ∪ D').card ≤ k := by
    rw [Finset.card_union_of_disjoint hAdisj']; omega
  have hQA₀ne : QA A₀ ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hA₀ hq)
  have hQDne : QA D ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hDsub hq)
  have hQD'ne : QA D' ≠ 0 := QA_ne_zero_of_two_le fun q hq => h2 q (hD'sub hq)
  have hrep1 : arcPt (QA A₀) (b : ℤ) + arcPt (QA D) a
      = arcPt (QA (A₀ ∪ D)) ((b : ℤ) * (QA D : ℤ) + a * (QA A₀ : ℤ)) := by
    rw [QA_union hAdisj, arcPt_add_denom hQA₀ne hQDne]
  have hrep2 : arcPt (QA A₀) (b' : ℤ) + arcPt (QA D') a'
      = arcPt (QA (A₀ ∪ D')) ((b' : ℤ) * (QA D' : ℤ) + a' * (QA A₀ : ℤ)) := by
    rw [QA_union hAdisj', arcPt_add_denom hQA₀ne hQD'ne]
  have hne' : arcPt (QA (A₀ ∪ D)) ((b : ℤ) * (QA D : ℤ) + a * (QA A₀ : ℤ))
      ≠ arcPt (QA (A₀ ∪ D')) ((b' : ℤ) * (QA D' : ℤ) + a' * (QA A₀ : ℤ)) := by
    rw [← hrep1, ← hrep2]
    exact shift_ne_of_arcPt_ne h2 hS hA₀ hD hD' hne
  rw [hrep1, hrep2]
  exact sigmaLe_separation h2 hS hAsub hA'sub hAcard hA'card hmax hne'

/-- **The translated torsion arcs around the points of `Σ_(A0)` are pairwise disjoint**
(Tao, `ortho-apply`(ii), the `p = ∞` paragraph, arXiv:2008.05066 §4): this discharges the
disjointness hypothesis `hdisj` of `opArc_sup_torsion_family`.

`S` is a finite set of pairwise coprime integers `≥ 2`, `A₀ ⊆ S` with `|A₀| ≤ k`, and
`D : ι → Finset ℕ` indexes the "complementary" arc sets: `D i ⊆ S \ A₀` with
`|D i| ≤ k - |A₀|`, so that the points `β + α i` (`β ∈ Σ_(⊆A₀)`, `α i = a i / Q_(D i)`) all lie
in `Tao's Σ_(≤k)`.  Under the `q_max^{-2k}`-separation `2ε < 1/q_max^{2k}` of Tao's `ortho`(i)
(the points of `Σ_(≤k)` are `q_max^{-2k}`-separated) the closed `ε`-neighbourhoods of the
translated torsion arcs `Σ_(⊆A₀) + α i` and `Σ_(⊆A₀) + α j` are disjoint.

The hypothesis `hinj` says that the arc points `α i` are pairwise distinct; it is needed (for
`α i = α j` the two translated arcs coincide) and is all that the proof uses about them. -/
theorem disjoint_torsionArc_shift {S : Finset ℕ} (h2 : ∀ q ∈ S, 2 ≤ q)
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q)
    {A₀ : Finset ℕ} (hA₀ : A₀ ⊆ S) {k : ℕ} (hk₀ : A₀.card ≤ k)
    {ι : Type*} [Fintype ι] (D : ι → Finset ℕ) (a : ι → ℤ)
    (hD : ∀ i, D i ⊆ S \ A₀) (hDk : ∀ i, (D i).card ≤ k - A₀.card)
    (hinj : ∀ i j, i ≠ j →
      Work.BourgainPlan.IonescuWainger.arcPt (Work.BourgainPlan.IonescuWainger.QA (D i)) (a i)
        ≠ Work.BourgainPlan.IonescuWainger.arcPt (Work.BourgainPlan.IonescuWainger.QA (D j)) (a j))
    {qmax : ℕ} (hmax : ∀ q ∈ S, q ≤ qmax) {ε : ℝ} (hε : 0 < ε)
    (hsep : 2 * ε < 1 / (qmax : ℝ) ^ (2 * k)) :
    ∀ i j : ι, i ≠ j →
      Disjoint (closure {ξ : Work.BourgainPlan.IonescuWainger.Circle |
          ∃ β ∈ Work.BourgainPlan.IonescuWainger.sigmaSubAFinset A₀,
          ξ - (β + Work.BourgainPlan.IonescuWainger.arcPt
              (Work.BourgainPlan.IonescuWainger.QA (D i)) (a i))
            ∈ Metric.closedBall (0 : Work.BourgainPlan.IonescuWainger.Circle) ε})
               (closure {ξ : Work.BourgainPlan.IonescuWainger.Circle |
          ∃ β ∈ Work.BourgainPlan.IonescuWainger.sigmaSubAFinset A₀,
          ξ - (β + Work.BourgainPlan.IonescuWainger.arcPt
              (Work.BourgainPlan.IonescuWainger.QA (D j)) (a j))
            ∈ Metric.closedBall (0 : Work.BourgainPlan.IonescuWainger.Circle) ε}) := by
  intro i j hij
  have hcl : ∀ c : 𝕋,
      closure {ξ : 𝕋 | ∃ β ∈ sigmaSubAFinset A₀, ξ - (β + c) ∈ Metric.closedBall (0 : 𝕋) ε}
        = {ξ : 𝕋 | ∃ β ∈ sigmaSubAFinset A₀, ξ - (β + c) ∈ Metric.closedBall (0 : 𝕋) ε} :=
    fun c => (isClosed_arcBall (sigmaSubAFinset A₀) c ε).closure_eq
  rw [hcl (arcPt (QA (D i)) (a i)), hcl (arcPt (QA (D j)) (a j))]
  rw [Set.disjoint_left]
  rintro ξ ⟨β, hβ, h1⟩ ⟨β', hβ', h2'⟩
  have hd1 : dist ξ (β + arcPt (QA (D i)) (a i)) ≤ ε := by
    have h := h1
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    rw [dist_eq_norm]
    exact h
  have hd2 : dist ξ (β' + arcPt (QA (D j)) (a j)) ≤ ε := by
    have h := h2'
    simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    rw [dist_eq_norm]
    exact h
  have hsep' : 1 / (qmax : ℝ) ^ (2 * k) ≤
      ‖(β + arcPt (QA (D i)) (a i)) - (β' + arcPt (QA (D j)) (a j))‖ :=
    shiftArc_separation h2 hS hA₀ hk₀ (hD i) (hD j) (hDk i) (hDk j) hmax (hinj i j hij) hβ hβ'
  have hdist : ‖(β + arcPt (QA (D i)) (a i)) - (β' + arcPt (QA (D j)) (a j))‖ ≤ 2 * ε := by
    rw [← dist_eq_norm]
    refine le_trans (dist_triangle _ ξ _) ?_
    rw [dist_comm]
    linarith
  linarith

end Work.IonescuWainger
