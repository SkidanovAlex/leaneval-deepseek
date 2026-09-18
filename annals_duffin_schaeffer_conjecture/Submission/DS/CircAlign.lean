import Submission.DS.CircleBridge

open scoped Nat ENNReal NNReal
open Set Filter MeasureTheory Metric
open DuffinSchaefferConjecture

/-!
# Per-denominator alignment: closed `≤` vs open `<` membership, a.e.

`mem_Acopr_iff_circle` (`CircCorr`) says: for `x ∈ (0,1)` with radius `δ = ψ(q)/q ≤ 1/2`,
`x ∈ Acopr ψ q` iff the circle-class of `x` lies within the **closed** ball of radius `δ`
around some reduced `m/q` (`m < q`, `gcd m q = 1`).  The open (`<`) membership differs
only on the spheres `‖·‖ = δ`, whose lifts to `(0,1)` are null
(`circle_boundary_measure_zero` + `volume_circle_eq_lift`, both in `CircBound` /
`CircleBridge`).  This file closes that gap: the two memberships agree almost everywhere
on `(0,1)`, per fixed `q`.
-/

namespace Submission.DS

/-- A sphere in the circle is measurable: it is the difference of the closed and the open
ball of the same radius. -/
lemma circle_sphere_measurableSet (c : AddCircle (1 : ℝ)) (r : ℝ) :
    MeasurableSet ({x : AddCircle (1 : ℝ) | ‖x - c‖ = r}) := by
  rw [sphere_eq_closedBall_sdiff_ball]
  exact (isClosed_closedBall.measurableSet).diff isOpen_ball.measurableSet

/-- Order-`n` points on the unit circle are exactly the classes of `m/n`,
`0 ≤ m < n` with `gcd m n = 1`; hence `approxAddOrderOf n δ` membership is the open
`< δ` counterpart of the closed sets used in `mem_Acopr_iff_circle`. -/
lemma approxAddOrderOf_mem_iff_open (n : ℕ) (hn : 0 < n) (δ : ℝ)
    (x : AddCircle (1 : ℝ)) :
    x ∈ approxAddOrderOf (AddCircle (1 : ℝ)) n δ ↔
      ∃ m : ℕ, m < n ∧ Nat.Coprime m n ∧
        ‖x - (((m : ℝ) / (n : ℝ)) : AddCircle (1 : ℝ))‖ < δ := by
  haveI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  rw [mem_approx_add_orderOf_iff]
  constructor
  · rintro ⟨y, hy, hx⟩
    have hord := (AddCircle.addOrderOf_eq_pos_iff (p := (1 : ℝ)) (u := y) hn).mp hy
    rcases hord with ⟨m, hm, hc, hyeq⟩
    refine ⟨m, hm, hc, ?_⟩
    have hyeq' : y = (((m : ℝ) / (n : ℝ)) : AddCircle (1 : ℝ)) := by
      rw [show (((m : ℝ) / (n : ℝ)) * (1 : ℝ) : ℝ) = (m : ℝ) / (n : ℝ) by ring] at hyeq
      simpa using hyeq.symm
    have hx' : ‖x - y‖ < δ := by simpa [dist_eq_norm] using hx
    rwa [hyeq'] at hx'
  · rintro ⟨m, hm, hc, hx⟩
    refine ⟨((m : ℝ) / (n : ℝ) : AddCircle (1 : ℝ)), ?_, ?_⟩
    · exact (AddCircle.addOrderOf_eq_pos_iff (p := (1 : ℝ)) (u := (((m : ℝ) / (n : ℝ)) : AddCircle (1 : ℝ))) hn).mpr
        ⟨m, hm, hc, by simp⟩
    · simpa [dist_eq_norm] using hx

/-- The lift to `(0,1)` of the boundary spheres `‖·‖ = r` around reduced `m/q` is null. -/
lemma lift_boundary_null (q : ℕ+) (r : NNReal) :
    volume ({x : ℝ | x ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ m : ℕ, m < (q : ℕ) ∧
      Nat.Coprime m (q : ℕ) ∧
      ‖((x : AddCircle (1 : ℝ)) - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ = (r : ℝ)}) = 0 := by
  classical
  let B : Fin (q : ℕ) → Set (AddCircle (1 : ℝ)) :=
    fun m => {x : AddCircle (1 : ℝ) | ‖x - (((m.1 : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ))‖ = (r : ℝ)}
  have hBmeas : ∀ m : Fin (q : ℕ), MeasurableSet (B m) := by
    intro m
    exact circle_sphere_measurableSet ((((m.1 : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ))) (r : ℝ)
  have hBvol : ∀ m : Fin (q : ℕ), volume (B m) = 0 := by
    intro m
    exact sphere_measure_zero ((((m.1 : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ))) (r : ℝ)
  let M : Set (AddCircle (1 : ℝ)) := ⋃ m : Fin (q : ℕ), B m
  have hMmeas : MeasurableSet M := by
    dsimp [M]
    exact MeasurableSet.iUnion hBmeas
  have hMvol : volume M = 0 := by
    apply le_antisymm _ bot_le
    calc
      volume M ≤ ∑' m : Fin (q : ℕ), volume (B m) := by
        dsimp [M]
        exact measure_iUnion_le B
      _ = 0 := by simp [hBvol]
  have hsub : ({x : ℝ | x ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ m : ℕ, m < (q : ℕ) ∧
      Nat.Coprime m (q : ℕ) ∧
      ‖((x : AddCircle (1 : ℝ)) - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ = (r : ℝ)} : Set ℝ)
      ⊆ (QuotientAddGroup.mk ⁻¹' M : Set ℝ) ∩ Set.Ioc (0 : ℝ) 1 := by
    intro x hx
    rcases hx with ⟨hxI, m, hmq, hcop, hn⟩
    constructor
    · dsimp [M]
      refine mem_iUnion.mpr ?_
      refine ⟨⟨m, hmq⟩, ?_⟩
      dsimp [B]
      simpa using hn
    · exact ⟨hxI.1, le_of_lt hxI.2⟩
  apply le_antisymm _ bot_le
  calc
    volume ({x : ℝ | x ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ m : ℕ, m < (q : ℕ) ∧
      Nat.Coprime m (q : ℕ) ∧
      ‖((x : AddCircle (1 : ℝ)) - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ = (r : ℝ)} : Set ℝ)
        ≤ volume ((QuotientAddGroup.mk ⁻¹' M : Set ℝ) ∩ Set.Ioc (0 : ℝ) 1) := measure_mono hsub
    _ = volume M := (volume_circle_eq_lift hMmeas).symm
    _ = 0 := hMvol

/-- For a fixed `q`, closed-`≤` membership in `Acopr ψ q` and the open-`<` circle
membership agree for almost every `x ∈ (0,1)`. -/
lemma Acopr_ae_eq_circle_open (ψ : ℕ+ → ℝ≥0) (q : ℕ+) (hδ : (ψ q / q : NNReal) ≤ (1 / 2 : NNReal)) :
    volume ((({x : ℝ | x ∈ Acopr ψ q} ∩ Set.Ioo (0 : ℝ) 1) \
      ({x : ℝ | ∃ m : ℕ, m < (q : ℕ) ∧ Nat.Coprime m (q : ℕ) ∧
        ‖((x : AddCircle (1 : ℝ)) - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ <
          ((ψ q / q : NNReal) : ℝ)} ∩ Set.Ioo (0 : ℝ) 1)) ∪
      (({x : ℝ | ∃ m : ℕ, m < (q : ℕ) ∧ Nat.Coprime m (q : ℕ) ∧
        ‖((x : AddCircle (1 : ℝ)) - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ <
          ((ψ q / q : NNReal) : ℝ)} ∩ Set.Ioo (0 : ℝ) 1) \
      ({x : ℝ | x ∈ Acopr ψ q} ∩ Set.Ioo (0 : ℝ) 1))) = 0 := by
  classical
  let r : NNReal := ψ q / q
  let I : Set ℝ := Set.Ioo (0 : ℝ) 1
  let A : Set ℝ := {x : ℝ | x ∈ Acopr ψ q}
  let B : Set ℝ := {x : ℝ | ∃ m : ℕ, m < (q : ℕ) ∧ Nat.Coprime m (q : ℕ) ∧
      ‖((x : AddCircle (1 : ℝ)) - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ < (r : ℝ)}
  let C : Set ℝ := {x : ℝ | ∃ m : ℕ, m < (q : ℕ) ∧ Nat.Coprime m (q : ℕ) ∧
      ‖((x : AddCircle (1 : ℝ)) - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ ≤ (r : ℝ)}
  let S : Set ℝ := {x : ℝ | x ∈ I ∧ ∃ m : ℕ, m < (q : ℕ) ∧ Nat.Coprime m (q : ℕ) ∧
      ‖((x : AddCircle (1 : ℝ)) - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ = (r : ℝ)}
  have hS : volume S = 0 := by
    simpa [S, I] using (lift_boundary_null q r)
  have hAcopr : A ∩ I = C ∩ I := by
    ext x
    constructor
    · intro hx
      have hxA : x ∈ Acopr ψ q := hx.1
      have hxI : x ∈ I := hx.2
      have hiff := (mem_Acopr_iff_circle q hxI.1 hxI.2 hδ)
      exact ⟨hiff.mp hxA, hxI⟩
    · intro hx
      have hxC : x ∈ C := hx.1
      have hxI : x ∈ I := hx.2
      have hiff := (mem_Acopr_iff_circle q hxI.1 hxI.2 hδ)
      exact ⟨hiff.mpr hxC, hxI⟩
  have hBsubC : B ⊆ C := by
    intro x hx
    rcases hx with ⟨m, hmq, hcop, hn⟩
    exact ⟨m, hmq, hcop, le_of_lt hn⟩
  have hBIsubAI : B ∩ I ⊆ A ∩ I := by
    intro x hx
    have hxI : x ∈ I := hx.2
    have hxC : x ∈ C := hBsubC hx.1
    rw [hAcopr]
    exact ⟨hxC, hxI⟩
  have hAB : (A ∩ I) \ (B ∩ I) ⊆ S := by
    intro x hx
    have hxA : x ∈ A := hx.1.1
    have hxI : x ∈ I := hx.1.2
    have hxnotB : x ∉ B := by
      intro hxB
      exact hx.2 ⟨hxB, hxI⟩
    have hxCI : x ∈ C ∩ I := by
      rw [← hAcopr]
      exact ⟨hxA, hxI⟩
    rcases hxCI.1 with ⟨m0, hm01, hm02, hm03⟩
    have hxnotB' : ¬ (∃ m : ℕ, m < (q : ℕ) ∧ Nat.Coprime m (q : ℕ) ∧
        ‖((x : AddCircle (1 : ℝ)) - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ < (r : ℝ)) := by
      simpa [B] using hxnotB
    exact ⟨hxI, ⟨m0, hm01, hm02, by
      apply le_antisymm hm03
      apply le_of_not_gt
      intro hlt
      exact hxnotB' ⟨m0, hm01, hm02, hlt⟩⟩⟩
  have hBA : (B ∩ I) \ (A ∩ I) ⊆ S := by
    intro x hx
    have hxAI : x ∈ A ∩ I := hBIsubAI hx.1
    exact False.elim (hx.2 hxAI)
  have hXsubS : (((A ∩ I) \ (B ∩ I)) ∪ ((B ∩ I) \ (A ∩ I))) ⊆ S := by
    intro x hx
    rcases hx with hx1 | hx2
    · exact hAB hx1
    · exact hBA hx2
  apply le_antisymm _ bot_le
  calc
    volume (((A ∩ I) \ (B ∩ I)) ∪ ((B ∩ I) \ (A ∩ I))) ≤ volume S := measure_mono hXsubS
    _ = 0 := hS

/-- The per-`q` ae-iff: for almost every `x ∈ (0,1)`, `x ∈ Acopr ψ q` iff the class of
`x` on the circle lies in the order-`q` open approximation set with radius `ψ(q)/q`. -/
lemma ae_eq_approxAddOrderOf (ψ : ℕ+ → ℝ≥0) (q : ℕ+) (hδ : (ψ q / q : NNReal) ≤ (1 / 2 : NNReal)) :
    ∀ᵐ x ∂volume, x ∈ Set.Ioo (0 : ℝ) 1 →
      (x ∈ Acopr ψ q ↔ (x : AddCircle (1 : ℝ)) ∈
        approxAddOrderOf (AddCircle (1 : ℝ)) (q : ℕ) ((ψ q / q : NNReal) : ℝ)) := by
  classical
  let A : Set ℝ := {x : ℝ | x ∈ Acopr ψ q}
  let B : Set ℝ := {x : ℝ | (x : AddCircle (1 : ℝ)) ∈
    approxAddOrderOf (AddCircle (1 : ℝ)) (q : ℕ) ((ψ q / q : NNReal) : ℝ)}
  let I : Set ℝ := Set.Ioo (0 : ℝ) 1
  have hB : ({x : ℝ | ∃ m : ℕ, m < (q : ℕ) ∧ Nat.Coprime m (q : ℕ) ∧
      ‖((x : AddCircle (1 : ℝ)) - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ <
        ((ψ q / q : NNReal) : ℝ)} : Set ℝ) = B := by
    ext x
    exact (approxAddOrderOf_mem_iff_open (q : ℕ) q.2 ((ψ q / q : NNReal) : ℝ)
      (x : AddCircle (1 : ℝ))).symm
  have hAlign := Acopr_ae_eq_circle_open ψ q hδ
  have hAlign' : volume (((A ∩ I) \ (B ∩ I)) ∪ ((B ∩ I) \ (A ∩ I))) = 0 := by
    have hset : ((A ∩ I) \ (B ∩ I)) ∪ ((B ∩ I) \ (A ∩ I)) =
        (({x : ℝ | x ∈ Acopr ψ q} ∩ I) \
          ({x : ℝ | ∃ m : ℕ, m < (q : ℕ) ∧ Nat.Coprime m (q : ℕ) ∧
            ‖((x : AddCircle (1 : ℝ)) - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ <
              ((ψ q / q : NNReal) : ℝ)} ∩ I)) ∪
        (({x : ℝ | ∃ m : ℕ, m < (q : ℕ) ∧ Nat.Coprime m (q : ℕ) ∧
            ‖((x : AddCircle (1 : ℝ)) - (((m : ℝ) / (q : ℝ)) : AddCircle (1 : ℝ)))‖ <
              ((ψ q / q : NNReal) : ℝ)} ∩ I) \ ({x : ℝ | x ∈ Acopr ψ q} ∩ I)) := by
      rw [← hB]
    rw [hset]
    exact hAlign
  have hbad : volume ({x : ℝ | x ∈ I ∧ ¬ (x ∈ A ↔ x ∈ B)}) = 0 := by
    have hset : ({x : ℝ | x ∈ I ∧ ¬ (x ∈ A ↔ x ∈ B)}) =
        ((A ∩ I) \ (B ∩ I)) ∪ ((B ∩ I) \ (A ∩ I)) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_diff]
      by_cases hxA : x ∈ A <;> by_cases hxB : x ∈ B <;> by_cases hxi : x ∈ I <;>
        simp [hxA, hxB, hxi]
    rw [hset]
    exact hAlign'
  rw [ae_iff]
  have hbad' : volume ({x : ℝ | ¬ (x ∈ I → (x ∈ A ↔ x ∈ B))}) = 0 := by
    have hset : ({x : ℝ | ¬ (x ∈ I → (x ∈ A ↔ x ∈ B))}) = {x : ℝ | x ∈ I ∧ ¬ (x ∈ A ↔ x ∈ B)} := by
      ext x
      simp only [Set.mem_setOf_eq]
      tauto
    rw [hset]
    exact hbad
  exact hbad'



/-- `E ψ`: the circle-level approximable set with radii `radSeq ψ`. -/
noncomputable def Eapprox (ψ : ℕ+ → ℝ≥0) : Set (AddCircle (1 : ℝ)) :=
  addWellApproximable (AddCircle (1 : ℝ)) (radSeq ψ)

/-- The per-denominator circle approximation sets are open, hence measurable. -/
lemma measurableSet_approxAddOrderOf_circle (n : ℕ) (δ : ℝ) :
    MeasurableSet (approxAddOrderOf (AddCircle (1 : ℝ)) n δ) := by
  unfold approxAddOrderOf
  exact (Metric.isOpen_thickening).measurableSet

/-- Membership in `E ψ` means lying in infinitely many order-`n` approximation sets. -/
lemma mem_Eapprox_iff_pos (ψ : ℕ+ → ℝ≥0) (x : AddCircle (1 : ℝ)) :
    x ∈ Eapprox ψ ↔
      {q : ℕ+ | x ∈ approxAddOrderOf (AddCircle (1 : ℝ)) (q : ℕ) (radSeq ψ (q : ℕ))}.Infinite := by
  unfold Eapprox addWellApproximable
  rw [← Nat.cofinite_eq_atTop]
  rw [cofinite.blimsup_set_eq]
  simp only [Set.mem_setOf_eq]
  have himg : {n : ℕ | 0 < n ∧ x ∈ approxAddOrderOf (AddCircle (1 : ℝ)) n (radSeq ψ n)} =
      (fun q : ℕ+ => (q : ℕ)) '' {q : ℕ+ | x ∈ approxAddOrderOf (AddCircle (1 : ℝ)) (q : ℕ) (radSeq ψ (q : ℕ))} := by
    ext n
    constructor
    · intro hn
      rcases hn with ⟨hpos, hx⟩
      exact ⟨⟨n, hpos⟩, hx, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, hq⟩
  rw [himg]
  constructor
  · intro h hfin
    exact h ((Set.finite_image_iff (Set.injOn_of_injective PNat.coe_injective
      (s := {q : ℕ+ | x ∈ approxAddOrderOf (AddCircle (1 : ℝ)) (q : ℕ) (radSeq ψ (q : ℕ))}))).mpr hfin)
  · intro hs hfim
    exact hs ((Set.finite_image_iff (Set.injOn_of_injective PNat.coe_injective
      (s := {q : ℕ+ | x ∈ approxAddOrderOf (AddCircle (1 : ℝ)) (q : ℕ) (radSeq ψ (q : ℕ))}))).1 hfim)

/-- Sets lying in infinitely many `S q` form a countable intersection of countable
unions (generic version over any type). -/
lemma infinite_mem_eq_iInter {β : Type*} (S : ℕ+ → Set β) :
    {x : β | {q : ℕ+ | x ∈ S q}.Infinite} = ⋂ N : ℕ, ⋃ q : ℕ+, (if (N : ℕ) ≤ (q : ℕ) then S q else ∅) := by
  classical
  ext x
  constructor
  · intro hx
    rw [mem_iInter]
    intro N
    have hN : ∃ q : ℕ+, (N : ℕ) ≤ (q : ℕ) ∧ x ∈ S q := by
      have h := (Submission.DS.infinite_iff_forall_ge {q : ℕ+ | x ∈ S q}).1 hx N
      rcases h with ⟨q, hq, hqN⟩
      exact ⟨q, hqN, hq⟩
    rcases hN with ⟨q, hqN, hxq⟩
    rw [mem_iUnion]
    exact ⟨q, by simp [hqN, hxq]⟩
  · intro hx
    change {q : ℕ+ | x ∈ S q}.Infinite
    rw [Submission.DS.infinite_iff_forall_ge]
    intro N
    have hN := (mem_iInter.mp hx) N
    rcases mem_iUnion.mp hN with ⟨q, hq⟩
    by_cases hc : (N : ℕ) ≤ (q : ℕ)
    · exact ⟨q, by simpa [hc] using hq, hc⟩
    · simp [hc] at hq

/-- `E ψ` is measurable: it is the limsup of open sets. -/
lemma E_measurableSet (ψ : ℕ+ → ℝ≥0) : MeasurableSet (Eapprox ψ) := by
  let S : ℕ+ → Set (AddCircle (1 : ℝ)) := fun q =>
    approxAddOrderOf (AddCircle (1 : ℝ)) (q : ℕ) (radSeq ψ (q : ℕ))
  have hS : ∀ q : ℕ+, MeasurableSet (S q) := by
    intro q
    simpa [S] using measurableSet_approxAddOrderOf_circle (q : ℕ) (radSeq ψ (q : ℕ))
  have hEq : Eapprox ψ = {x : AddCircle (1 : ℝ) | {q : ℕ+ | x ∈ S q}.Infinite} := by
    ext x
    simpa [S] using mem_Eapprox_iff_pos ψ x
  rw [hEq]
  rw [infinite_mem_eq_iInter (β := AddCircle (1 : ℝ)) (S := S)]
  refine MeasurableSet.iInter (fun N : ℕ => ?_)
  refine MeasurableSet.iUnion (fun q : ℕ+ => ?_)
  by_cases h : (N : ℕ) ≤ (q : ℕ)
  · simp [h]
    exact hS q
  · simp [h]

end Submission.DS
