import Mathlib
import Submission.Work.Serre.Models
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.Serre.serreS2OfC0C2oddS1
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.Serre.subsingleton_homotopyFibre_of_piMapN

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Connectivity of the homotopy fibre (`Work.Stems.homotopyFibre_conn`)

Let `f : Sⁿ → X` be a map which is a bijection on `πₙ` and such that `π_i(X) = 0` for every
`i ≠ n` (i.e. `X` is a `K(πₙ(X), n)` as far as homotopy groups are concerned).  Then the homotopy
fibre of `f` is `n`-connected: `π_j(F) = 0` for every `j ≤ n`.

Classically this is the familiar statement that the homotopy fibre of `Sⁿ → K(πₙ(X),n)` — the
`(n-1)`-connected cover of `Sⁿ` — is `n`-connected.  The proof is the long exact sequence of the
fibration `F → Sⁿ → X` (`Work.RatHurewicz.pair_les`):

* in degrees `j ≤ n - 1` the statement is `Work.Serre.subsingleton_homotopyFibre_of_piMapN`
  (an `N`-connected map has `(N-1)`-connected fibre), applied with `N = n`;
* in degree `n` one uses the two *extra* inputs which are special to the situation: the
  *injectivity* of `πₙ(f)` (`ker d = im πₙ(f) = πₙ(X)` makes the connecting map `d : π_{n+1}(X) →
  πₙ(F)` trivial, so `πₙ(F) → πₙ(Sⁿ)` is injective) and the *surjectivity* of `π_{n+1}(f)` (which is
  free because `π_{n+1}(X) = 0`): the induced map `πₙ(F) → πₙ(Sⁿ)` is then the zero map, so
  `πₙ(F) = 0`.

Both are instances of the general lemma `Work.Stems.subsingleton_homotopyFibre_of_inj_surj` below,
which is the form of `Work.Serre.subsingleton_homotopyFibre_of_piMapN` in which the two degrees
`N` and `N+1` of the hypothesis are used *separately* (injectivity at `≤ N`, surjectivity at
`≤ N+1`) rather than through the uniform bijectivity hypothesis.
-/

open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

/-- **Injectivity in degrees `≤ N` and surjectivity in degrees `≤ N+1` make the homotopy fibre
`N`-connected.**  Same proof as `Work.Serre.subsingleton_homotopyFibre_of_piMapN`, with the two
hypotheses split: only injectivity of `π_i(g)` for `i ≤ N` and surjectivity for `i ≤ N + 1` are
used (the degree `N+1` is needed only for surjectivity, which is what makes the top degree work). -/
theorem subsingleton_homotopyFibre_of_inj_surj {B Γ : Type} [TopologicalSpace B]
    [TopologicalSpace Γ] (g : C(Γ, B)) (N : ℕ) (hN : 1 ≤ N) (γ : Γ)
    (hinj : ∀ i : ℕ, i ≤ N → Function.Injective (Work.Serre.piMapN g i γ))
    (hsurj : ∀ i : ℕ, i ≤ N + 1 → Function.Surjective (Work.Serre.piMapN g i γ)) :
    ∀ k : ℕ, k ≤ N → Subsingleton (HomotopyGroup (Fin k)
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
          (hinj 0 (Nat.zero_le N)) ha)
        (by rw [← Work.Serre.piMapN_eq_pimap g 0 γ]; exact hsurj 1 (by omega))
    have hZ : Subsingleton (ZerothHomotopy (Work.RatHurewicz.homotopyFibre g γ)) :=
      (pathConnectedSpace_iff_zerothHomotopy.mp hpc).2
    exact (HomotopyGroup.pi0EquivZerothHomotopy
      (x := Work.RatHurewicz.homotopyFibreBasepoint g γ)).injective (hZ.elim _ _)
  · rcases eq_or_lt_of_le (show 1 ≤ k from hkpos) with hk1 | hk2
    · -- `k = 1`
      subst hk1
      exact Work.Serre.piOneHomotopyFibreSubsingleton_of_surjective g γ
        (by rw [← Work.Serre.piMapN_eq_pimap g 0 γ]; exact hinj 1 hN)
        (by rw [← Work.Serre.piMapN_eq_pimap g 1 γ]; exact hsurj 2 (by omega))
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
          (⟨Work.Serre.unitIntervalOneSub, Work.Serre.continuous_unitIntervalOneSub⟩ : C(I, I)).comp ContinuousMap.fst
        let ev : C(C(I, B) × I, B) := ⟨fun z => z.1 z.2, continuous_eval⟩
        let cm : C(I × Work.RatHurewicz.homotopyFibre g γ, B) :=
          ev.comp (pathCm.prodMk timeCm)
        have hcm2 : ∀ (t : I) (p : Work.RatHurewicz.homotopyFibre g γ),
            cm.toFun (t, p) = p.1.2.1 (Work.Serre.unitIntervalOneSub t) := fun t p => rfl
        refine ⟨ContinuousMap.Homotopy.mk cm ?_ ?_⟩
        · intro p
          rw [hcm2 0 p, Work.Serre.unitIntervalOneSub_zero]
          exact p.2
        · intro p
          rw [hcm2 1 p, Work.Serre.unitIntervalOneSub_one]
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
        refine (hinj (j + 2) (by omega)) ?_
        rw [Work.Serre.piMapN_eq_pimap g (j + 1) γ]
        exact h1'
      -- the connecting map `d : π_{j+3}(B) → π_{j+2}(F)` is trivial
      have hd : ∀ x : HomotopyGroup (Fin (j + 3)) B (g γ), d x = 1 := by
        intro x
        obtain ⟨z, hz⟩ := hsurj (j + 3) (by omega) x
        refine (h3 x).mpr ⟨z, ?_⟩
        rw [← Work.Serre.piMapN_eq_pimap g (j + 2) γ]
        exact hz
      refine ⟨fun y z => ?_⟩
      have hy : y = 1 := by
        obtain ⟨x, hx⟩ := (h4 y).mp (hι y)
        rw [← hx, hd x]
      have hz : z = 1 := by
        obtain ⟨x, hx⟩ := (h4 z).mp (hι z)
        rw [← hx, hd x]
      rw [hy, hz]

/-- **The homotopy fibre of a `πₙ`-bijective map into a space with `π_i = 0` for `i ≠ n` is
`n`-connected.** -/
theorem homotopyFibre_conn {X : Type} [TopologicalSpace X] {n : ℕ} (hn : 3 ≤ n)
    (f : C(Work.Serre.Sph n, X)) (s₀ : Work.Serre.Sph n)
    (hbij : Function.Bijective (Work.Serre.piMapN f n s₀))
    (hX : ∀ i, i ≠ n → Subsingleton (HomotopyGroup (Fin i) X (f s₀))) :
    ∀ j : ℕ, j ≤ n → Subsingleton (HomotopyGroup (Fin j)
      (Work.RatHurewicz.homotopyFibre f s₀) (Work.RatHurewicz.homotopyFibreBasepoint f s₀)) := by
  intro j hj
  refine subsingleton_homotopyFibre_of_inj_surj f n (by omega) s₀ ?_ ?_ j hj
  · -- injectivity in degrees `≤ n`: below `n` the source `π_i(Sⁿ)` is trivial, at `n` it is `hbij`
    intro i hi
    by_cases hin : i = n
    · subst hin
      exact hbij.1
    · haveI : Subsingleton (HomotopyGroup (Fin i) (Work.Serre.Sph n) s₀) :=
        Work.Stems.sphereConnectivity n i (by omega) s₀
      exact fun a b _ => Subsingleton.elim a b
  · -- surjectivity in degrees `≤ n + 1`: away from `n` the target `π_i(X)` is trivial
    intro i hi
    by_cases hin : i = n
    · subst hin
      exact hbij.2
    · haveI : Subsingleton (HomotopyGroup (Fin i) X (f s₀)) := hX i hin
      exact fun y => ⟨default, Subsingleton.elim _ y⟩

end

end Work.Stems
