import Mathlib
import Submission.Work.WilE2.KhoGood
import Submission.Work.WilE2.exists_meet_components_iUnion
import Submission.Work.WilE8.Basic
import Submission.Work.WilE7.fiber_card_bound
import Submission.Work.WilE9.Ift.OneShot.exists_clean

set_option autoImplicit false

namespace Work.WilE2

open WilkiesDesign WilkiesDesign.E

/-- `Polynomial.eval` of the "successor polynomial" `(X + 1) * p + 1`. -/
private lemma eval_succPoly (p : Polynomial ℕ) (n : ℕ) :
    (((Polynomial.X : Polynomial ℕ) + 1) * p + 1).eval n = (n + 1) * p.eval n + 1 := by
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one]

/-- The point set of a semi-Pfaffian set is the union of the cubes over its basic disjuncts. -/
private lemma semiPf_set_eq_iUnion {k : ℕ} (X : SemiPf k) :
    (⋃ i : Fin X.basics.length, (cubeC k ∩ {x | (X.basics.get i).holds X.c x})) = X.set := by
  ext x
  rw [SemiPf.set]
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hx, hhold⟩
    exact ⟨hx, X.basics.get i, List.get_mem X.basics i, hhold⟩
  · rintro ⟨hx, B, hB, hhold⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hB
    exact ⟨i, hx, hhold⟩

/-- Sum bound: if every disjunct has degree `≥ 1` then the sum of `p` over the disjuncts is at
most `(X.deg + 1) * p X.deg`. -/
private lemma sum_eval_deg_le {k : ℕ} (X : SemiPf k) (p : Polynomial ℕ)
    (hge : ∀ B ∈ X.basics, 1 ≤ B.deg) :
    (∑ i : Fin X.basics.length, p.eval ((X.basics.get i).deg)) ≤ (X.deg + 1) * p.eval X.deg := by
  have hle : ∀ i : Fin X.basics.length, p.eval ((X.basics.get i).deg) ≤ p.eval X.deg := by
    intro i
    apply Work.WilE7.eval_mono_nat
    exact List.le_sum_of_mem (List.mem_map_of_mem (f := Basic.deg) (List.get_mem X.basics i))
  have h1 : (∑ i : Fin X.basics.length, p.eval ((X.basics.get i).deg)) ≤
      ∑ _i : Fin X.basics.length, p.eval X.deg := Finset.sum_le_sum (fun i _ => hle i)
  have h2 : (∑ _i : Fin X.basics.length, p.eval X.deg) = X.basics.length * p.eval X.deg := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  have hlen : X.basics.length ≤ X.deg := by
    have h := List.length_le_sum_of_one_le (X.basics.map Basic.deg) (by
      intro i hi
      obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hi
      exact hge B hB)
    simpa [SemiPf.deg, List.length_map] using h
  rw [h2] at h1
  exact h1.trans (Nat.mul_le_mul_right _ (by omega))

theorem E2_components_of_basic
    (hbasic : ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r)
      (B : WilkiesDesign.E.Basic k r), k + r ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval (WilkiesDesign.E.Basic.deg B) ∧
        (↑s : Set (Fin k → ℝ)) ⊆
          WilkiesDesign.E.cubeC k ∩ {x | WilkiesDesign.E.Basic.holds c B x} ∧
        ∀ x ∈ WilkiesDesign.E.cubeC k ∩ {x | WilkiesDesign.E.Basic.holds c B x}, ∃ y ∈ s,
          connectedComponentIn
              (WilkiesDesign.E.cubeC k ∩ {x | WilkiesDesign.E.Basic.holds c B x}) x
            = connectedComponentIn
              (WilkiesDesign.E.cubeC k ∩ {x | WilkiesDesign.E.Basic.holds c B x}) y) :
    ∀ F : ℕ, ∃ p : Polynomial ℕ, ∀ (k : ℕ) (X : WilkiesDesign.E.SemiPf k), X.fmt ≤ F →
      ∃ s : Finset (Fin k → ℝ), s.card ≤ p.eval X.deg ∧
        (↑s : Set (Fin k → ℝ)) ⊆ X.set ∧
        ∀ x ∈ X.set, ∃ y ∈ s,
          connectedComponentIn X.set x = connectedComponentIn X.set y := by
  intro F
  obtain ⟨p, hp⟩ := hbasic F
  refine ⟨(Polynomial.X + 1) * p + 1, ?_⟩
  intro k X hFmt
  have hF : k + X.r ≤ F := hFmt
  by_cases hzero : ∃ B ∈ X.basics, B.deg = 0
  · -- some disjunct imposes no condition: `X.set` is the whole cube, a single point suffices
    have hset : X.set = cubeC k :=
      Work.WilE9.Ift.OneShot.semiPf_set_eq_cubeC_of_mem_deg_zero hzero
    refine ⟨{0}, ?_, ?_, ?_⟩
    · rw [Finset.card_singleton, eval_succPoly]
      omega
    · rw [Finset.coe_singleton, Set.singleton_subset_iff, hset]
      exact Work.WilE8.zero_mem_cubeC k
    · intro x hx
      refine ⟨0, Finset.mem_singleton_self 0, ?_⟩
      have hx' : x ∈ cubeC k := by rw [← hset]; exact hx
      rw [hset,
        IsPreconnected.connectedComponentIn (Work.WilE8.cubeC_preconnected k) hx',
        IsPreconnected.connectedComponentIn (Work.WilE8.cubeC_preconnected k)
          (Work.WilE8.zero_mem_cubeC k)]
  · -- every disjunct has degree `≥ 1`: combine the per-disjunct component sets
    have hge : ∀ B ∈ X.basics, 1 ≤ B.deg :=
      fun B hB => Nat.one_le_iff_ne_zero.mpr (fun hz => hzero ⟨B, hB, hz⟩)
    obtain ⟨s, hcard, hsub, hcov⟩ :=
      Work.WilE2.exists_meet_components_iUnion
        (fun i : Fin X.basics.length => cubeC k ∩ {x | (X.basics.get i).holds X.c x})
        (fun i : Fin X.basics.length => p.eval (X.basics.get i).deg)
        (by intro i; exact hp k X.r X.c (X.basics.get i) hF)
    have hUnion := semiPf_set_eq_iUnion X
    refine ⟨s, ?_, ?_, ?_⟩
    · rw [eval_succPoly]
      have hcount := sum_eval_deg_le X p hge
      exact hcard.trans (hcount.trans (Nat.le_succ _))
    · rw [hUnion] at hsub; exact hsub
    · intro x hx
      rw [← hUnion] at hx ⊢
      exact hcov x hx

end Work.WilE2
