import Mathlib
import Submission.Work.WilE7.graphCell_subPf
import Submission.Work.WilE7.LevelFibre.levelFibre_subPf
import Submission.Work.WilE7.SheetData.DefsX
import Submission.Work.WilE7.SheetData.NonstrictLevelFibre
import Submission.Work.WilE7.SheetData.NonstrictLevelIncl
import Submission.Work.WilE7.projFirst_fiberClosure

namespace Work.WilE7.SheetData

open WilkiesConjecture WilkiesDesign WilkiesDesign.E
open Work.WilE7.LevelFibre

/-- **The identification.**  Under the sheet data (`hsub`/`hcov` say that for `x ∈ C` the fibre of
`X.set` over `x` is exactly the `k`-element set `{s j x}`; `hcard` says that fibre has exactly `k`
points; `hlvl` says the level map `j ↦ (s j x) (Fin.last m)` is non-decreasing), the set

```
lfY3 = {y | init y ∈ C ∧ ∃ z : Fin k → ℝ^{p+(m+1)}, z l ∈ X.set, π z l = init y,
            levels of z non-decreasing, z pairwise distinct, level (z i) = y (last p)}
```

is exactly the graph cell `{y | Fin.init y ∈ C ∧ y (Fin.last p) = (s i (Fin.init y)) (Fin.last m)}`.

For `x ∈ C` the fibre is the `k`-element set `{s j x}` and both `l ↦ level (z l)` and
`j ↦ level (s j x)` enumerate the levels of the fibre; both are non-decreasing, so they agree
(`List.Perm.eq_of_sortedLE` applied to the sorted enumerations). -/
theorem lfY3_eq_graphCell {p m M k : ℕ} (X : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (XC : WilkiesDesign.E.SemiPf (p + M)) (C : Set (Fin p → ℝ))
    (hC : C = WilkiesDesign.E.projFirst p M '' XC.set)
    (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
    (hcov : ∀ z ∈ X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hcard : ∀ x ∈ C, (WilkiesDesign.E.fiber X.set x).ncard = k)
    (hlvl : ∀ x ∈ C, Monotone fun j : Fin k => (s j x) (Fin.last m))
    (i : Fin k) :
    lfY3 (p := p) (q := m + 1) (M := M) (k := k) (Fin.last m) i X XC =
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        y (Fin.last p) = (s i (Fin.init y)) (Fin.last m)} := by
  ext y
  constructor
  · -- `lfY3 ⊆` the graph cell: the order-statistic argument
    rintro ⟨⟨w, hw⟩, z, hzX, hzproj, hzmono, hzdist, hzpin⟩
    have hxC : Fin.init y ∈ C := by
      rw [hC]
      exact ⟨Fin.append (Fin.init y) w, hw, Work.WilE7.projFirst_append _ _⟩
    refine ⟨hxC, ?_⟩
    -- the fibre over `Fin.init y` is the range of the sheets
    have hzfib : ∀ l : Fin k,
        WilkiesDesign.E.projSnd p (m + 1) (z l) ∈ WilkiesDesign.E.fiber X.set (Fin.init y) := by
      intro l
      show Fin.append (Fin.init y) (WilkiesDesign.E.projSnd p (m + 1) (z l)) ∈ X.set
      rw [← hzproj l, Work.WilE7.append_projFirst_projSnd]
      exact hzX l
    have hfib : WilkiesDesign.E.fiber X.set (Fin.init y) =
        Set.range (fun j : Fin k => s j (Fin.init y)) := by
      ext u
      constructor
      · intro hu
        obtain ⟨j, hj⟩ := hcov (Fin.append (Fin.init y) u) hu
          (by rw [Work.WilE7.projFirst_append]; exact hxC)
        refine ⟨j, ?_⟩
        rw [Work.WilE7.projFirst_append] at hj
        rw [Work.WilE7.projSnd_append] at hj
        simpa using hj
      · rintro ⟨j, rfl⟩
        exact hsub j (Fin.init y) hxC
    -- every `z l` is a sheet value
    have hpre : ∀ l : Fin k, ∃ j : Fin k, z l = Fin.append (Fin.init y) (s j (Fin.init y)) := by
      intro l
      have hmem : WilkiesDesign.E.projSnd p (m + 1) (z l) ∈
          Set.range (fun j : Fin k => s j (Fin.init y)) := by
        rw [← hfib]
        exact hzfib l
      obtain ⟨j, hj⟩ := hmem
      refine ⟨j, ?_⟩
      calc z l = Fin.append (WilkiesDesign.E.projFirst p (m + 1) (z l))
            (WilkiesDesign.E.projSnd p (m + 1) (z l)) :=
            (Work.WilE7.append_projFirst_projSnd (z l)).symm
        _ = Fin.append (Fin.init y) (WilkiesDesign.E.projSnd p (m + 1) (z l)) := by
            rw [hzproj l]
        _ = Fin.append (Fin.init y) (s j (Fin.init y)) := by rw [← hj]
    choose σ hσ using hpre
    have hσinj : Function.Injective σ := by
      intro l l' h
      by_contra hne
      exact hzdist l l' hne (by rw [hσ l, hσ l', h])
    have hσsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hσinj
    let σe : Fin k ≃ Fin k := Equiv.ofBijective σ ⟨hσinj, hσsurj⟩
    -- the two level families are `b` and `b ∘ σ`
    have hcomp : (fun l : Fin k => (z l) (Fin.natAdd p (Fin.last m))) =
        fun l : Fin k => (s (σ l) (Fin.init y)) (Fin.last m) := by
      funext l
      rw [hσ l, Fin.append_right]
    have hmapσ : Multiset.map (fun l : Fin k => σ l) (Finset.univ : Finset (Fin k)).val =
        (Finset.univ : Finset (Fin k)).val := by
      have h3 := Finset.map_val σe.toEmbedding (Finset.univ : Finset (Fin k))
      rw [Finset.map_univ_equiv σe] at h3
      exact h3.symm
    have hmult : Multiset.map (fun l : Fin k => (z l) (Fin.natAdd p (Fin.last m)))
          (Finset.univ : Finset (Fin k)).val =
        Multiset.map (fun j : Fin k => (s j (Fin.init y)) (Fin.last m))
          (Finset.univ : Finset (Fin k)).val := by
      rw [hcomp]
      rw [show (fun l : Fin k => (s (σ l) (Fin.init y)) (Fin.last m)) =
          (fun j : Fin k => (s j (Fin.init y)) (Fin.last m)) ∘ σ from rfl]
      rw [← Multiset.map_map, hmapσ]
    -- sorted enumerations of the same multiset coincide
    have hperm := Multiset.coe_eq_coe.mp (show
      (((List.ofFn fun l : Fin k => (z l) (Fin.natAdd p (Fin.last m))) : List ℝ) : Multiset ℝ) =
        ((List.ofFn fun j : Fin k => (s j (Fin.init y)) (Fin.last m)) : List ℝ) from by
      rw [List.ofFn_eq_map, List.ofFn_eq_map, ← Multiset.map_coe, ← Multiset.map_coe]
      rw [show (↑(List.finRange k) : Multiset (Fin k)) = (Finset.univ : Finset (Fin k)).val
        from rfl]
      exact hmult)
    have hsortf : (List.ofFn fun l : Fin k => (z l) (Fin.natAdd p (Fin.last m))).SortedLE :=
      List.sortedLE_iff_pairwise.mpr
        (List.pairwise_ofFn.mpr fun l l' hlt => hzmono l l' hlt)
    have hsortb : (List.ofFn fun j : Fin k => (s j (Fin.init y)) (Fin.last m)).SortedLE :=
      List.sortedLE_iff_pairwise.mpr
        (List.pairwise_ofFn.mpr fun j j' hlt => hlvl (Fin.init y) hxC (le_of_lt hlt))
    have hEq := List.Perm.eq_of_sortedLE hsortf hsortb hperm
    have hfuneq : (fun l : Fin k => (z l) (Fin.natAdd p (Fin.last m))) =
        fun j : Fin k => (s j (Fin.init y)) (Fin.last m) := List.ofFn_inj.mp hEq
    rw [← hzpin]
    exact congrFun hfuneq i
  · -- the graph cell `⊆ lfY3`: the canonical witnesses
    rintro ⟨hxC, hylast⟩
    have hxC' : Fin.init y ∈ WilkiesDesign.E.projFirst p M '' XC.set := by rwa [hC] at hxC
    obtain ⟨ζ, hζ, hζeq⟩ := hxC'
    refine ⟨⟨WilkiesDesign.E.projSnd p M ζ, ?_⟩,
      fun l => Fin.append (Fin.init y) (s l (Fin.init y)), ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hζeq, Work.WilE7.append_projFirst_projSnd]
      exact hζ
    · intro l
      exact hsub l (Fin.init y) hxC
    · intro l
      exact Work.WilE7.projFirst_append _ _
    · intro l l' hll
      change (Fin.append (Fin.init y) (s l (Fin.init y))) (Fin.natAdd p (Fin.last m)) ≤
        (Fin.append (Fin.init y) (s l' (Fin.init y))) (Fin.natAdd p (Fin.last m))
      rw [Fin.append_right, Fin.append_right]
      exact hlvl (Fin.init y) hxC (le_of_lt hll)
    · intro l l' hne hcontra
      apply hne
      apply hinj (Fin.init y) hxC
      have h2 := congrArg (WilkiesDesign.E.projSnd p (m + 1)) hcontra
      rwa [Work.WilE7.projSnd_append, Work.WilE7.projSnd_append] at h2
    · change (Fin.append (Fin.init y) (s i (Fin.init y))) (Fin.natAdd p (Fin.last m)) =
        y (Fin.last p)
      rw [Fin.append_right]
      exact hylast.symm

theorem graphCellSubPfX {p m : ℕ} (X : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (C : Set (Fin p → ℝ)) (hCpf : WilkiesDesign.E.SubPf p C)
    (k : ℕ) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hinj : ∀ x ∈ C, Function.Injective fun j : Fin k => s j x)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ X.set)
    (hcov : ∀ z ∈ X.set, WilkiesDesign.E.projFirst p (m + 1) z ∈ C →
      ∃ j : Fin k, s j (WilkiesDesign.E.projFirst p (m + 1) z) =
        WilkiesDesign.E.projSnd p (m + 1) z)
    (hcard : ∀ x ∈ C, (WilkiesDesign.E.fiber X.set x).ncard = k)
    (hlvl : ∀ x ∈ C, Monotone fun j : Fin k => (s j x) (Fin.last m))
    (i : Fin k) :
    WilkiesDesign.E.SubPf (p + 1)
      {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        y (Fin.last p) = (s i (Fin.init y)) (Fin.last m)} := by
  obtain ⟨M, XC, hC⟩ := hCpf
  rw [← lfY3_eq_graphCell X XC C hC s hinj hsub hcov hcard hlvl i]
  exact nonstrictLevel_subPf i (Fin.last m) X XC

end Work.WilE7.SheetData
