import Mathlib
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.Serre.piOneHomotopyFibreSubsingleton
import Submission.Work.Serre.pathConnectedSpace_homotopyFibre
import Submission.Work.Serre.cylRelPi

/-!
# The homotopy fibre of an `N`-connected map is `(N-1)`-connected

`Work.Serre.subsingleton_homotopyFibre_of_piMapN`: if `g : C(Γ,B)` induces a bijection on `π_i` at
every base point for every `i ≤ N` (with `1 ≤ N`), then for every `γ : Γ` the homotopy fibre
`homotopyFibre g γ` has trivial `π_k` for `k ≤ N - 1`.

The proof is the long exact sequence of the pair (`Work.RatHurewicz.pair_les`, which is stated for
an arbitrary map), in the form

  `π_k(F) → π_k(Γ) → π_k(B) → π_{k-1}(F) → π_{k-1}(Γ)`

for `F = homotopyFibre g γ`: the projection `π_k(F) → π_k(Γ)` is trivial (`g ∘ fst` is
null-homotopic, and `π_k(Γ) → π_k(B)` is injective), and the connecting map `π_k(B) → π_{k-1}(F)`
is trivial (`π_k(Γ) → π_k(B)` is surjective).  Degrees `0` and `1` are handled separately, as in
`Work.Serre.rwRelPiVanishingOfPiBijective`.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

/-- `Work.Serre.piMapN` in degree `n + 1` is `Work.StemsB.πmap` in degree `n`. -/
theorem piMapN_eq_pimap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (k : ℕ) (x : X) : piMapN f (k + 1) x = Work.StemsB.πmap f k x :=
  funext (fun a => by
    induction a using Quotient.inductionOn with
    | h p => rfl)

theorem subsingleton_homotopyFibre_of_piMapN {B Γ : Type} [TopologicalSpace B]
    [TopologicalSpace Γ] (g : C(Γ, B)) (N : ℕ) (hN : 1 ≤ N) (γ : Γ)
    (hg : ∀ i : ℕ, i ≤ N → ∀ γ : Γ, Function.Bijective (piMapN g i γ)) :
    ∀ k : ℕ, k ≤ N - 1 → Subsingleton (HomotopyGroup (Fin k)
      (Work.RatHurewicz.homotopyFibre g γ)
      (Work.RatHurewicz.homotopyFibreBasepoint g γ)) := by
  intro k hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: the homotopy fibre is path connected
    subst hk0
    refine ⟨fun u v => ?_⟩
    have hpc : PathConnectedSpace (Work.RatHurewicz.homotopyFibre g γ) :=
      Work.Serre.pathConnectedSpace_homotopyFibre g γ
        (fun a ha => Work.Serre.joined_of_piMapN_zero_injective g γ
          (hg 0 (Nat.zero_le N) γ).1 ha)
        (by rw [← piMapN_eq_pimap g 0 γ]; exact (hg 1 hN γ).2)
    have hZ : Subsingleton (ZerothHomotopy (Work.RatHurewicz.homotopyFibre g γ)) :=
      (pathConnectedSpace_iff_zerothHomotopy.mp hpc).2
    exact (HomotopyGroup.pi0EquivZerothHomotopy
      (x := Work.RatHurewicz.homotopyFibreBasepoint g γ)).injective (hZ.elim _ _)
  · rcases eq_or_lt_of_le (show 1 ≤ k from hkpos) with hk1 | hk2
    · -- `k = 1`
      subst hk1
      exact Work.Serre.piOneHomotopyFibreSubsingleton_of_surjective g γ
        (by rw [← piMapN_eq_pimap g 0 γ]; exact (hg 1 hN γ).1)
        (by rw [← piMapN_eq_pimap g 1 γ]; exact (hg 2 (by omega) γ).2)
    · -- `k = j + 2` with `j ≥ 0`
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      obtain ⟨del, d, h1, h2, h3, h4⟩ := Work.RatHurewicz.pair_les g γ (j + 1) (by omega)
      -- the composite `g ∘ homotopyFibreFst` is null-homotopic
      have hnull : ∃ y : B, (g.comp (Work.RatHurewicz.homotopyFibreFst g γ)).Homotopic
          (ContinuousMap.const (Work.RatHurewicz.homotopyFibre g γ) y) := by
        refine ⟨g γ, ?_⟩
        let pathF : C(Work.RatHurewicz.homotopyFibre g γ, C(I, B)) :=
          ⟨fun p => p.1.2.1,
            continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)⟩
        let pathCm : C(I × Work.RatHurewicz.homotopyFibre g γ, C(I, B)) :=
          pathF.comp ContinuousMap.snd
        let timeCm : C(I × Work.RatHurewicz.homotopyFibre g γ, I) :=
          (⟨unitIntervalOneSub, continuous_unitIntervalOneSub⟩ : C(I, I)).comp ContinuousMap.fst
        let ev : C(C(I, B) × I, B) := ⟨fun z => z.1 z.2, continuous_eval⟩
        let cm : C(I × Work.RatHurewicz.homotopyFibre g γ, B) :=
          ev.comp (pathCm.prodMk timeCm)
        have hcm2 : ∀ (t : I) (p : Work.RatHurewicz.homotopyFibre g γ),
            cm.toFun (t, p) = p.1.2.1 (unitIntervalOneSub t) := fun t p => rfl
        refine ⟨ContinuousMap.Homotopy.mk cm ?_ ?_⟩
        · intro p
          rw [hcm2 0 p, unitIntervalOneSub_zero]
          exact p.2
        · intro p
          rw [hcm2 1 p, unitIntervalOneSub_one]
          exact p.1.2.2
      -- the projection `π_{j+2}(F) → π_{j+2}(Γ)` is trivial
      have hι : ∀ y : HomotopyGroup (Fin (j + 2)) (Work.RatHurewicz.homotopyFibre g γ)
          (Work.RatHurewicz.homotopyFibreBasepoint g γ),
          Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst g γ) (j + 1)
            (Work.RatHurewicz.homotopyFibreBasepoint g γ) y = 1 := by
        intro y
        have h1' : Work.StemsB.πmap (g.comp (Work.RatHurewicz.homotopyFibreFst g γ)) (j + 1)
            (Work.RatHurewicz.homotopyFibreBasepoint g γ) y = 1 :=
          Work.Serre.πmap_eq_one_of_homotopic_const _ (j + 1) _ hnull y
        rw [Work.StemsB.πmap_comp_apply (Work.RatHurewicz.homotopyFibreFst g γ) g (j + 1)
          (Work.RatHurewicz.homotopyFibreBasepoint g γ) y] at h1'
        refine (hg (j + 2) (by omega) γ).1 ?_
        rw [piMapN_eq_pimap g (j + 1) γ]
        exact h1'
      -- the connecting map `d : π_{j+3}(B) → π_{j+2}(F)` is trivial
      have hd : ∀ x : HomotopyGroup (Fin (j + 3)) B (g γ), d x = 1 := by
        intro x
        obtain ⟨z, hz⟩ := (hg (j + 3) (by omega) γ).2 x
        refine (h3 x).mpr ⟨z, ?_⟩
        rw [← piMapN_eq_pimap g (j + 2) γ]
        exact hz
      refine ⟨fun y z => ?_⟩
      have hy : y = 1 := by
        obtain ⟨x, hx⟩ := (h4 y).mp (hι y)
        rw [← hx, hd x]
      have hz : z = 1 := by
        obtain ⟨x, hx⟩ := (h4 z).mp (hι z)
        rw [← hx, hd x]
      rw [hy, hz]

end

end Work.Serre
