import Mathlib
import Submission.Work.Cohomology.exists_cycle_cross
import Submission.Work.Cohomology.Pairing
import Submission.Work.Cohomology.exists_chain_eval_ne_zero
import Submission.Work.Cohomology.H_cupOf_mk
import Submission.Work.Cohomology.ezChainB_sum_cycle_clean

open Submission.Cohomology CategoryTheory

namespace Work.Cohomology

/-- A sorry-free replacement for `Work.Cohomology.exists_cycle_cross`, proved from the
independently established shuffle-cycle lemma `Work.Cohomology.ezChainB_sum_cycle_clean`
instead of from the (currently still open) `Work.Cohomology.ezChainB_sum_cycle`.

For cycles `c` of `X` and `d` of `Y` it produces a cycle `ω` of `X ⊗ Y` such that the cup
product of the pullbacks of arbitrary cocycles `u`, `v` pairs with `ω` to `⟨u,c⟩ · ⟨v,d⟩`. -/
theorem exists_cycle_cross_local {X Y : SSet.{0}} {p q : ℕ}
    (c : Submission.Cohomology.SChain X ℚ p) (d : Submission.Cohomology.SChain Y ℚ q)
    (hc : c ∈ Submission.Cohomology.chainCycles X ℚ p)
    (hd : d ∈ Submission.Cohomology.chainCycles Y ℚ q) :
    ∃ ω : Submission.Cohomology.SChain
        (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ (p + q),
      ω ∈ Submission.Cohomology.chainCycles
        (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ (p + q) ∧
      ∀ (u : Submission.Cohomology.Cochain X ℚ p) (v : Submission.Cohomology.Cochain Y ℚ q),
        Submission.Cohomology.coboundary X ℚ p u = 0 →
        Submission.Cohomology.coboundary Y ℚ q v = 0 →
        Submission.Cohomology.seval
          (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ (p + q)
          (Submission.Cohomology.cupOf
            (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ rfl
            (Submission.Cohomology.pullbackCo ℚ
              (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) u)
            (Submission.Cohomology.pullbackCo ℚ
              (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) v)) ω
          = Submission.Cohomology.seval X ℚ p u c * Submission.Cohomology.seval Y ℚ q v d := by
  refine ⟨∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB a b, ?_, ?_⟩
  · exact ezChainB_sum_cycle_clean c d hc hd
  · intro u v hu hv
    have hucyc : u ∈ Submission.Cohomology.cycles X ℚ p :=
      (Submission.Cohomology.mem_cycles_iff u).mpr hu
    have hvcyc : v ∈ Submission.Cohomology.cycles Y ℚ q :=
      (Submission.Cohomology.mem_cycles_iff v).mpr hv
    obtain ⟨u₁, hu₁c, hu₁n, hu₁b⟩ := normalized_rep u hucyc
    obtain ⟨v₁, hv₁c, hv₁n, hv₁b⟩ := normalized_rep v hvcyc
    rw [seval_cup_eq_of_cohomologous
        (ω := ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB a b)
        (hω := ezChainB_sum_cycle_clean c d hc hd)
        (u := u) (u' := u₁) (v := v) (v' := v₁)
        hucyc hvcyc hu₁c hv₁c hu₁b hv₁b]
    rw [seval_eq_of_sub_mem_boundaries c hc hu₁b,
        seval_eq_of_sub_mem_boundaries d hd hv₁b]
    exact ezChainB_sum_pairing c d u₁ v₁ hu₁c hv₁c hu₁n hv₁n

/-- **The cross product of two nonzero classes is nonzero.**  For nonzero cohomology classes
`x : H X ℚ p`, `y : H Y ℚ q` of two simplicial sets, their external cup product
`pr₁^*x ⌣ pr₂^*y` on the cartesian product `X ⊗ Y` is nonzero — over `ℚ`.

Proof plan.  By `Work.Cohomology.exists_chain_eval_ne_zero` applied to representatives `u` of `x`
and `v` of `y`, there are cycles `c` of `X`, `d` of `Y` with `seval u c ≠ 0 ≠ seval v d`.
`Work.Cohomology.exists_cycle_cross` then produces a cycle `ω` of `X ⊗ Y` with
`seval (pr₁^*u ⌣ pr₂^*v) ω = seval u c * seval v d ≠ 0`, which is a nonzero multiple over `ℚ`
(`mul_ne_zero`).  If the class of the cross product were zero, then by
`Submission.Cohomology.pairMap_mk`/`pairMap` its pairing with every cycle — in particular with `ω`
— would vanish, a contradiction. -/
theorem H_cup_cross_ne_zero {X Y : SSet.{0}} {p q : ℕ} (x : Submission.Cohomology.H X ℚ p)
    (y : Submission.Cohomology.H Y ℚ q) (hx : x ≠ 0) (hy : y ≠ 0) :
    Submission.Cohomology.H.cup p q
      (Submission.Cohomology.H.map ℚ (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) p x)
      (Submission.Cohomology.H.map ℚ (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) q y)
      ≠ 0 := by
  let T : SSet.{0} := MonoidalCategoryStruct.tensorObj X Y
  let F : T ⟶ X := SemiCartesianMonoidalCategory.fst X Y
  let G : T ⟶ Y := SemiCartesianMonoidalCategory.snd X Y
  -- Representatives of the two classes.
  let u : Cochain X ℚ p := (Quot.out x).1
  have hu : u ∈ cycles X ℚ p := (Quot.out x).2
  have hux : H.mk u hu = x := Quot.out_eq x
  let v : Cochain Y ℚ q := (Quot.out y).1
  have hv : v ∈ cycles Y ℚ q := (Quot.out y).2
  have hvy : H.mk v hv = y := Quot.out_eq y
  have hux0 : H.mk u hu ≠ 0 := by rw [hux]; exact hx
  have hvy0 : H.mk v hv ≠ 0 := by rw [hvy]; exact hy
  -- Non-degeneracy over the field `ℚ`: a nonzero class pairs nontrivially with some cycle.
  obtain ⟨c, hc, hcne⟩ := Work.Cohomology.exists_chain_eval_ne_zero u hu hux0
  obtain ⟨d, hd, hdne⟩ := Work.Cohomology.exists_chain_eval_ne_zero v hv hvy0
  -- The cycle-level cross product, on which the cup product takes the value `⟨u,c⟩·⟨v,d⟩`.
  obtain ⟨ω, hω, hωeq⟩ := exists_cycle_cross_local c d hc hd
  have hne : seval T ℚ (p + q)
        (cupOf T ℚ rfl (pullbackCo ℚ F u) (pullbackCo ℚ G v)) ω ≠ 0 := by
    rw [hωeq u v hu hv]
    exact mul_ne_zero hcne hdne
  -- Identify the cross product with the class of the chain-level cup product.
  rw [← hux, ← hvy, H.map_mk, H.map_mk]
  change H.cupOf rfl (H.mk (pullbackCo ℚ (SemiCartesianMonoidalCategory.fst X Y) u) _)
      (H.mk (pullbackCo ℚ (SemiCartesianMonoidalCategory.snd X Y) v) _) ≠ 0
  rw [Work.Cohomology.H_cupOf_mk]
  -- If that class were zero, its pairing with `ω` would vanish, contradicting `hne`.
  intro hzero
  have h1 : pairMap T (p + q)
      (H.mk (cupOf T ℚ rfl (pullbackCo ℚ (SemiCartesianMonoidalCategory.fst X Y) u)
              (pullbackCo ℚ (SemiCartesianMonoidalCategory.snd X Y) v))
        (cupOf_mem_cycles (R := ℚ) rfl
          (pullbackCo_mem_cycles (SemiCartesianMonoidalCategory.fst X Y) hu)
          (pullbackCo_mem_cycles (SemiCartesianMonoidalCategory.snd X Y) hv)))
      ⟨ω, hω⟩ = 0 := by
    rw [hzero, map_zero, LinearMap.zero_apply]
  rw [pairMap_mk] at h1
  exact hne h1

end Work.Cohomology
