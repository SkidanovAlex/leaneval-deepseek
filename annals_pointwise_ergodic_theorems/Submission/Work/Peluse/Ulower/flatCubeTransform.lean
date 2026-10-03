import Mathlib
import Submission.Work.Peluse.Ulower.flatCubeSumForm
import Submission.Work.Peluse.Ulower.flatCubeBlind

/-!
# The flat-cube transform

Peluse's Lemma 7.5 uses the step: the `2 ^ s`-th power of the box norm of the level-`s` cube term
of `g` is bounded by the `2 ^ s`-th power of the box norm of `g` itself.  This is the "flat cube
transform" of the Krause--Mirek--Tao programme.

The proof runs as follows.  Writing `Q = arithIcc 1 D` and reindexing the two sums over the `s`-fold
product `Q ^ s` as flat cube sums (`flatCubeSumForm`), the statement becomes

`NPow s W ≤ C · NPow s ψ`,  where `W v = cubeTerm h v g 0` and `ψ v = g (∑ i, v i)`,

and then

`W v = ∏_{α : Fin s → Bool} Φ_α v`,  `Φ_α v = star ^ |α| (g (cornerShift h v α))`,  `ψ = Φ_0`,

each `Φ_α` (for `α ≠ 0`) being *blind* in a coordinate in which `α` is `true`, and `‖Φ_α‖ ≤ 1`.
The blind-factor inequality `npowBlindProd` then lets the factors `Φ_α`, `α ≠ 0`, be dropped one by
one from the flat cube sum, leaving `NPow s (Φ_0) = NPow s ψ`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

theorem flatCubeTransform (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (D : ℕ) (h : Fin s → ℤ) (g : ℤ → ℂ),
        1 ≤ D → (∀ t : ℤ, ‖g t‖ ≤ 1) →
        ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
            ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
              (Work.Peluse.cubeTerm h (Work.Peluse.Concat.mix ω v0 v1) g 0)‖
        ≤ C * ‖∑ v0 ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
          ∑ v1 ∈ Fintype.piFinset (fun _ : Fin s => Work.Peluse.arithIcc 1 D),
            ∏ ω : Fin s → Bool, (star^[Work.Peluse.weight ω])
              (g (Work.Peluse.cornerShift v1 v0 ω))‖ := by
  refine ⟨1, one_pos, ?_⟩
  intro D h g hD hg
  classical
  haveI hne : Nonempty ↥(Work.Peluse.arithIcc 1 D) := by
    refine ⟨⟨1, ?_⟩⟩
    rw [Work.Peluse.arithIcc, Finset.mem_image]
    exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hD⟩, by norm_num⟩
  obtain ⟨hL, hR⟩ := flatCubeSumForm s hs D h g
  let W : (Fin s → ↥(Work.Peluse.arithIcc 1 D)) → ℂ :=
    fun v => Work.Peluse.cubeTerm h (fun i => (v i).1) g 0
  let Ps : (Fin s → ↥(Work.Peluse.arithIcc 1 D)) → ℂ :=
    fun v => g (∑ i : Fin s, (v i).1)
  let Phi : (Fin s → Bool) → (Fin s → ↥(Work.Peluse.arithIcc 1 D)) → ℂ :=
    fun α v =>
      (star^[Work.Peluse.weight α]) (g (Work.Peluse.cornerShift h (fun i => (v i).1) α))
  have hW : W = fun v => ∏ α : Fin s → Bool, Phi α v := by
    funext v
    simp only [W, Phi, Work.Peluse.cubeTerm, zero_add]
  have hPs : Ps = Phi (fun _ : Fin s => false) := by
    funext v
    simp only [Ps, Phi, Work.Peluse.cornerShift, Work.Peluse.weight]
    simp
  have hPhi : ∀ (α : Fin s → Bool) (v : Fin s → ↥(Work.Peluse.arithIcc 1 D)), ‖Phi α v‖ ≤ 1 := by
    intro α v
    rw [show Phi α v = (star^[Work.Peluse.weight α])
        (g (Work.Peluse.cornerShift h (fun i => (v i).1) α)) from rfl]
    rw [norm_star_iterate]
    exact hg _
  have hblindPhi : ∀ α : Fin s → Bool, α ≠ (fun _ => false) → ∃ i : Fin s,
      ∀ (v : Fin s → ↥(Work.Peluse.arithIcc 1 D)) (u : ↥(Work.Peluse.arithIcc 1 D)),
        Phi α (Function.update v i u) = Phi α v := by
    intro α hα
    have hex : ∃ i : Fin s, α i = true := by
      by_contra hcon
      apply hα
      funext i
      cases hi : α i with
      | false => rfl
      | true => exact absurd ⟨i, hi⟩ hcon
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, ?_⟩
    intro v u
    have hc : Work.Peluse.cornerShift h (fun j => (Function.update v i u j).1) α
        = Work.Peluse.cornerShift h (fun j => (v j).1) α := by
      unfold Work.Peluse.cornerShift
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j = i
      · rw [hj, hi]
        simp
      · simp only []
        rw [Function.update_of_ne hj]
    simp only [Phi, hc]
  have key := npowBlindProd (t := s) hs (X := ↥(Work.Peluse.arithIcc 1 D)) Phi hPhi hblindPhi
    (Finset.univ.erase (fun _ : Fin s => false)) (Phi (fun _ : Fin s => false))
    (fun α hα => (Finset.mem_erase.mp hα).1)
  have hprod : ∀ v : Fin s → ↥(Work.Peluse.arithIcc 1 D),
      Phi (fun _ : Fin s => false) v
        * (∏ α ∈ Finset.univ.erase (fun _ : Fin s => false), Phi α v)
        = ∏ α : Fin s → Bool, Phi α v := by
    intro v
    exact Finset.mul_prod_erase Finset.univ (fun α : Fin s → Bool => Phi α v)
      (Finset.mem_univ (fun _ : Fin s => false))
  have hfull : (fun v : Fin s → ↥(Work.Peluse.arithIcc 1 D) =>
        Phi (fun _ : Fin s => false) v
          * ∏ α ∈ Finset.univ.erase (fun _ : Fin s => false), Phi α v)
      = fun v => ∏ α : Fin s → Bool, Phi α v := funext hprod
  have hmain : Work.Peluse.Concat.NPow s W ≤ Work.Peluse.Concat.NPow s Ps := by
    rw [hW, hPs, ← hfull]
    exact key
  rw [hL, hR]
  show Work.Peluse.Concat.NPow s W ≤ 1 * Work.Peluse.Concat.NPow s Ps
  rw [one_mul]
  exact hmain

end

end Work.Peluse.Ulower
