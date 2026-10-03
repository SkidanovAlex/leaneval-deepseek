import Mathlib
import Submission.Work.OROneRel.bandUpBlockDict
import Submission.Work.OROneRel.britton_hnnConjMap_injective
import Submission.Work.OROneRel.prod_conj_telescope

namespace Work.OROneRel

/-!
# The up-block lemma `(♠)` from Britton for the band pair `(tlH, tlLowTau)`

This file proves `Work.OROneRel.bandUpBlockHk_of_hnnConjMap_injective`: the band-vertex ("two
guard") up-block statement `(♠)` of `Submission/Work/OROneRel/bandUpBlock.lean`, *conditional on the
injectivity of the HNN comparison map* of the band pair `(tlH p q Wt, tlLowTau p q)`.

The walk `t : Fin n → ℤ` with letters `y i ∈ tlHk (t i)`, `t 0 = t (n-1) = b` and the two guards at
the turns is transported to the HNN word

  `h 0 * τ^{δ 1} * h 1 * ⋯ * τ^{δ (n-1)} * h (n-1)`  (`h i = τ^{-t i} * y i * τ^{t i} ∈ tlH`,
   `δ i = t i - t (i-1)`),

whose product is `τ^{-b} * (∏ y) * τ^b`.  The two guards are exactly the no-pinch conditions of the
HNN word (`Work.OROneRel.not_mem_hnnEdgeA_of_not_mem_tlAk_sub_one`,
`Work.OROneRel.not_mem_hnnEdgeB_of_not_mem_tlAk`), so
`Work.OROneRel.britton_hnnConjMap_injective` finishes.

The telescoping identity used to pass from the walk form to the HNN word form is
`Work.OROneRel.prod_conj_telescope`.
-/

/-- The sign `t (j+1) - t j ∈ {±1}` attached to the gap after the `j`-th letter, as a unit, for a
`±1` level walk `t`. -/
noncomputable def bubSign {n : ℕ} (t : Fin n → ℤ) : Fin (n - 1) → ℤˣ :=
  fun j => if t ⟨j.1 + 1, by omega⟩ = t ⟨j.1, by omega⟩ + 1 then 1 else -1

theorem bubSign_eq_one_iff {n : ℕ} (t : Fin n → ℤ) (j : Fin (n - 1)) :
    (bubSign t j = 1) ↔ t ⟨j.1 + 1, by omega⟩ = t ⟨j.1, by omega⟩ + 1 := by
  unfold bubSign
  by_cases h : t ⟨j.1 + 1, by omega⟩ = t ⟨j.1, by omega⟩ + 1
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp [h]

/-- The underlying integer of the sign of a `±1` step is the step difference. -/
theorem bubSign_val {n : ℕ} (t : Fin n → ℤ)
    (hstep : ∀ j : Fin (n - 1), t ⟨j.1 + 1, by omega⟩ = t ⟨j.1, by omega⟩ + 1 ∨
      t ⟨j.1 + 1, by omega⟩ = t ⟨j.1, by omega⟩ - 1)
    (j : Fin (n - 1)) : (bubSign t j : ℤ) = t ⟨j.1 + 1, by omega⟩ - t ⟨j.1, by omega⟩ := by
  rcases hstep j with h | h
  · rw [bubSign_eq_one_iff t j |>.mpr h]; simp [h]
  · have hne : ¬ (t ⟨j.1 + 1, by omega⟩ = t ⟨j.1, by omega⟩ + 1) := by rw [h]; omega
    rw [show bubSign t j = -1 from by unfold bubSign; rw [if_neg hne]]
    simp [h]

/-- `blkPrev` at a nonfirst index is the previous level. -/
theorem blkPrev_fin_succ {n : ℕ} (hn : 1 ≤ n) (t : Fin n → ℤ) (b : ℤ) (j : ℕ) (hj : j + 1 < n) :
    blkPrev b hn t ⟨j + 1, hj⟩ = t ⟨j, by omega⟩ := by
  unfold blkPrev
  rw [if_neg]
  · congr 1
  · intro h
    have := congrArg Fin.val h
    simp at this

/-- `blkNext` at an index with a successor is the next level. -/
theorem blkNext_fin_succ {n : ℕ} (t : Fin n → ℤ) (b : ℤ) (j : ℕ) (hj : j + 1 < n) :
    blkNext b t ⟨j, by omega⟩ = t ⟨j + 1, hj⟩ := by
  unfold blkNext
  rw [dif_pos hj]

/-- **The no-pinch condition from the two guards.**  Transporting the `±1` walk to the HNN word form
`h 0 τ^{δ 1} h 1 ⋯ τ^{δ (n-1)} h (n-1)` (`h i = τ^{-t i} y i τ^{t i}`), the two guards are exactly
the no-pinch conditions at the turns. -/
theorem noPinch_bubWord (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (b : ℤ) {n : ℕ} (hn : 2 ≤ n)
    (t : Fin n → ℤ) (y : Fin n → FreeGroup (Fin 2))
    (hstep : ∀ i : Fin (n - 1), t ⟨i.1 + 1, by omega⟩ = t ⟨i.1, by omega⟩ + 1 ∨
      t ⟨i.1 + 1, by omega⟩ = t ⟨i.1, by omega⟩ - 1)
    (hh : Fin n → ↥(tlH p q Wt))
    (hh_spec : ∀ i, (hh i : FreeGroup (Fin 2)) = (tlLowTau p q hp hq hcop) ^ (-(t i)) * y i *
      (tlLowTau p q hp hq hcop) ^ (t i))
    (hpeak : ∀ i : Fin n, blkPrev b (by omega) t i = t i - 1 →
      blkNext b t i = t i - 1 →
      y i ∉ tlAk p q hp hq hcop Wt (t i - 1))
    (hvalley : ∀ i : Fin n, blkPrev b (by omega) t i = t i + 1 →
      blkNext b t i = t i + 1 →
      y i ∉ tlAk p q hp hq hcop Wt (t i)) :
    NoPinch (tlH p q Wt) (tlLowTau p q hp hq hcop)
      (List.ofFn (fun j : Fin (n - 1) => (bubSign t j, hh ⟨j.1, by omega⟩))) := by
  rw [NoPinch, List.isChain_ofFn]
  intro i hi
  rw [not_and]
  intro hmem hsign
  change hh ⟨i + 1, by omega⟩ ∈
      hnnEdgeSubBase (tlH p q Wt) (tlLowTau p q hp hq hcop) (bubSign t ⟨i, by omega⟩) at hmem
  change bubSign t ⟨i + 1, hi⟩ = -(bubSign t ⟨i, by omega⟩) at hsign
  rcases Int.units_eq_one_or (bubSign t ⟨i, by omega⟩) with hs | hs
  · -- peak: the walk rises at `i` and falls at `i+1`
    have hti : t ⟨i + 1, by omega⟩ = t ⟨i, by omega⟩ + 1 :=
      (bubSign_eq_one_iff t ⟨i, by omega⟩).mp hs
    have hsign' : bubSign t ⟨i + 1, hi⟩ = -1 := by rw [hs] at hsign; simpa using hsign
    have hmemA : ((hh ⟨i + 1, by omega⟩ : ↥(tlH p q Wt)) : FreeGroup (Fin 2)) ∈
        hnnEdgeA (tlH p q Wt) (tlLowTau p q hp hq hcop) := by
      rw [hs] at hmem
      simp only [hnnEdgeSubBase_one] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    have hti2 : t ⟨i + 2, by omega⟩ = t ⟨i + 1, by omega⟩ - 1 := by
      rcases hstep ⟨i + 1, hi⟩ with h | h
      · exfalso
        have : bubSign t ⟨i + 1, hi⟩ = 1 := (bubSign_eq_one_iff t ⟨i + 1, hi⟩).mpr h
        rw [this] at hsign'; exact absurd hsign' (by decide)
      · exact h
    have hpv : blkPrev b (by omega) t ⟨i + 1, by omega⟩ = t ⟨i + 1, by omega⟩ - 1 := by
      rw [blkPrev_fin_succ]; omega
    have hnx : blkNext b t ⟨i + 1, by omega⟩ = t ⟨i + 1, by omega⟩ - 1 := by
      rw [blkNext_fin_succ (t := t) (b := b) (j := i + 1) (by omega)]; omega
    have hg := hpeak ⟨i + 1, by omega⟩ hpv hnx
    exact (not_mem_hnnEdgeA_of_not_mem_tlAk_sub_one p q hp hq hcop Wt
      (hh_spec ⟨i + 1, by omega⟩) hg) hmemA
  · -- valley: the walk falls at `i` and rises at `i+1`
    have hsign' : bubSign t ⟨i + 1, hi⟩ = 1 := by rw [hs] at hsign; simpa using hsign
    have hti : t ⟨i + 1, by omega⟩ = t ⟨i, by omega⟩ - 1 := by
      rcases hstep ⟨i, by omega⟩ with h | h
      · exfalso
        have : bubSign t ⟨i, by omega⟩ = 1 := (bubSign_eq_one_iff t ⟨i, by omega⟩).mpr h
        rw [this] at hs; exact absurd hs (by decide)
      · exact h
    have hti2 : t ⟨i + 2, by omega⟩ = t ⟨i + 1, by omega⟩ + 1 :=
      (bubSign_eq_one_iff t ⟨i + 1, hi⟩).mp hsign'
    have hmemB : ((hh ⟨i + 1, by omega⟩ : ↥(tlH p q Wt)) : FreeGroup (Fin 2)) ∈
        hnnEdgeB (tlH p q Wt) (tlLowTau p q hp hq hcop) := by
      rw [hs] at hmem
      simp only [hnnEdgeSubBase_neg_one] at hmem
      exact Subgroup.mem_subgroupOf.mp hmem
    have hpv : blkPrev b (by omega) t ⟨i + 1, by omega⟩ = t ⟨i + 1, by omega⟩ + 1 := by
      rw [blkPrev_fin_succ]; omega
    have hnx : blkNext b t ⟨i + 1, by omega⟩ = t ⟨i + 1, by omega⟩ + 1 := by
      rw [blkNext_fin_succ (t := t) (b := b) (j := i + 1) (by omega)]; omega
    have hg := hvalley ⟨i + 1, by omega⟩ hpv hnx
    exact (not_mem_hnnEdgeB_of_not_mem_tlAk p q hp hq hcop Wt
      (hh_spec ⟨i + 1, by omega⟩) hg) hmemB

theorem bandUpBlockHk_of_hnnConjMap_injective (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (hW0 : Wt 0 = 1)
    (hcoh : ∀ i : ℤ, Work.OROneRel.cohom (Work.OROneRel.tlW p q) (Wt i) = Multiplicative.ofAdd i)
    (hwin : ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Work.OROneRel.tlU p q)),
      Work.OROneRel.coverEdge e ∈ Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (htree : ∀ i : ℤ, 0 ≤ i → i ≤ (p : ℤ) * (q : ℤ) →
      ∀ e ∈ Work.OROneRel.decor (Work.OROneRel.tlW p q) 0 (Work.OROneRel.wordOf (Wt i)),
        Work.OROneRel.coverEdge e ∈ Work.OROneRel.winTree Wt (Work.OROneRel.tlW p q) 0 ((p : ℤ) * (q : ℤ)))
    (hInj : Function.Injective (Work.OROneRel.hnnConjMap (Work.OROneRel.tlH p q Wt)
      (Work.OROneRel.tlLowTau p q hp hq hcop)))
    (b : ℤ) {n : ℕ} (hn : 2 ≤ n) (t : Fin n → ℤ) (y : Fin n → FreeGroup (Fin 2))
    (hbase : t ⟨0, by omega⟩ = b) (hlast : t ⟨n - 1, by omega⟩ = b)
    (hge : ∀ i, b ≤ t i)
    (hstep : ∀ i : Fin (n - 1), t ⟨i.1 + 1, by omega⟩ = t ⟨i.1, by omega⟩ + 1 ∨
      t ⟨i.1 + 1, by omega⟩ = t ⟨i.1, by omega⟩ - 1)
    (hy : ∀ i, y i ∈ Work.OROneRel.tlHk p q hp hq hcop Wt (t i))
    (hpeak : ∀ i : Fin n, Work.OROneRel.blkPrev b (by omega) t i = t i - 1 →
      Work.OROneRel.blkNext b t i = t i - 1 →
      y i ∉ Work.OROneRel.tlAk p q hp hq hcop Wt (t i - 1))
    (hvalley : ∀ i : Fin n, Work.OROneRel.blkPrev b (by omega) t i = t i + 1 →
      Work.OROneRel.blkNext b t i = t i + 1 →
      y i ∉ Work.OROneRel.tlAk p q hp hq hcop Wt (t i)) :
    (List.ofFn y).prod ∉ Work.OROneRel.tlHk p q hp hq hcop Wt b := by
  intro hP
  have hn1 : 1 ≤ n := by omega
  have hmemH : ∀ i : Fin n,
      (tlLowTau p q hp hq hcop) ^ (-(t i)) * y i * (tlLowTau p q hp hq hcop) ^ (t i)
        ∈ tlH p q Wt :=
    fun i => (mem_tlHk_iff_bandUpBlock p q hp hq hcop Wt (t i) (y i)).mp (hy i)
  let hh : Fin n → ↥(tlH p q Wt) := fun i =>
    ⟨(tlLowTau p q hp hq hcop) ^ (-(t i)) * y i * (tlLowTau p q hp hq hcop) ^ (t i), hmemH i⟩
  have hh_spec : ∀ i, (hh i : FreeGroup (Fin 2)) =
      (tlLowTau p q hp hq hcop) ^ (-(t i)) * y i * (tlLowTau p q hp hq hcop) ^ (t i) :=
    fun i => rfl
  let L : List (ℤˣ × ↥(tlH p q Wt)) :=
    List.ofFn (fun j : Fin (n - 1) => (bubSign t j, hh ⟨j.1, by omega⟩))
  have hnoPinch : NoPinch (tlH p q Wt) (tlLowTau p q hp hq hcop) L := by
    dsimp only [L]
    exact noPinch_bubWord p q hp hq hcop Wt b hn t y hstep hh hh_spec hpeak hvalley
  have hword_mem : hnnWord (tlH p q Wt) (tlLowTau p q hp hq hcop) L ∈ tlH p q Wt := by
    have hPb : (tlLowTau p q hp hq hcop) ^ (-b) * (List.ofFn y).prod *
        (tlLowTau p q hp hq hcop) ^ b ∈ tlH p q Wt :=
      (mem_tlHk_iff_bandUpBlock p q hp hq hcop Wt b (List.ofFn y).prod).mp hP
    have htel := prod_conj_telescope (M := FreeGroup (Fin 2)) (tlLowTau p q hp hq hcop) hn1 t
      (fun i => (hh i : FreeGroup (Fin 2)))
    have hLHS : (List.ofFn (fun i : Fin n => (tlLowTau p q hp hq hcop) ^ (t i) *
        (hh i : FreeGroup (Fin 2)) * (tlLowTau p q hp hq hcop) ^ (-(t i)))).prod
        = (List.ofFn y).prod := by
      apply congrArg List.prod
      rw [List.ofFn_inj]
      funext i
      dsimp only [hh]
      group
    rw [hLHS, hbase, hlast] at htel
    have hW : (List.ofFn (fun j : Fin (n - 1) => (hh ⟨j.1, by omega⟩ : FreeGroup (Fin 2)) *
        (tlLowTau p q hp hq hcop) ^ (t ⟨j.1 + 1, by omega⟩ - t ⟨j.1, by omega⟩))).prod *
        (hh ⟨n - 1, by omega⟩ : FreeGroup (Fin 2)) =
        (tlLowTau p q hp hq hcop) ^ (-b) * (List.ofFn y).prod *
          (tlLowTau p q hp hq hcop) ^ b := by
      rw [htel]; group
    have hword_eq : hnnWord (tlH p q Wt) (tlLowTau p q hp hq hcop) L =
        (List.ofFn (fun j : Fin (n - 1) => (hh ⟨j.1, by omega⟩ : FreeGroup (Fin 2)) *
          (tlLowTau p q hp hq hcop) ^
            (t ⟨j.1 + 1, by omega⟩ - t ⟨j.1, by omega⟩))).prod := by
      dsimp only [L]
      rw [hnnWord, List.map_ofFn]
      apply congrArg List.prod
      rw [List.ofFn_inj]
      funext j
      simp only [Function.comp_apply, Prod.fst, Prod.snd]
      rw [bubSign_val t hstep j]
    rw [hword_eq]
    have hfin : (List.ofFn (fun j : Fin (n - 1) => (hh ⟨j.1, by omega⟩ : FreeGroup (Fin 2)) *
        (tlLowTau p q hp hq hcop) ^ (t ⟨j.1 + 1, by omega⟩ - t ⟨j.1, by omega⟩))).prod =
        ((tlLowTau p q hp hq hcop) ^ (-b) * (List.ofFn y).prod *
          (tlLowTau p q hp hq hcop) ^ b) * (hh ⟨n - 1, by omega⟩ : FreeGroup (Fin 2))⁻¹ := by
      rw [← hW]; group
    rw [hfin]
    exact Subgroup.mul_mem _ hPb (Subgroup.inv_mem _ (hh ⟨n - 1, by omega⟩).2)
  have hnil : L = [] :=
    britton_hnnConjMap_injective (tlH p q Wt) (tlLowTau p q hp hq hcop) hInj L hnoPinch hword_mem
  have hlen : L.length = n - 1 := by dsimp only [L]; simp
  rw [hnil] at hlen
  simp only [List.length_nil] at hlen
  omega

end Work.OROneRel
