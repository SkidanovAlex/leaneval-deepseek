import Mathlib
import Submission.Work.KMTAreas.A4Z.SivLocal
import Submission.Work.KMTAreas.A4.Struct
import Submission.Work.KMTAreas.A4.eLpNorm_AhalfTranspose_le
import Submission.Work.KMTAreas.A4.eLpNorm_count_eq_lp_norm
import Submission.Work.KMTAreas.A4.eLpNorm_le_of_l1_and_bounded
import Submission.Work.KMTAreas.A4.eLpNorm_two_le_of_interp
import Submission.Work.KMTAreas.A4.kmtProjEqSelf
import Submission.Work.KMTAreas.A5.logbPowLeConstMulRpow

/-!
# `T = (1 - Π_{≤l,≤d(l-Log N)}) Ã_N^{**}(·,h)` commutes with a finite block sum

The operator `transOp P ρ N l = (1 - Π_{≤l,≤d(l-Log N)}) Ã_N^{**}(·,h)` of §5.2 is *linear* in its
first argument (the argument against which the second dual function `Ã_N^{**} = AhalfTranspose₂` is
taken); this module records exactly that, in the form needed by the `siv-second` assembly: for any
finite set `S` of blocks,

`T (∑_{i∈S} f·1_{I_i}) = ∑_{i∈S} T (f·1_{I_i}) = ∑_{i∈S} minorPart P ρ N l f h i`.

The three ingredients are

* `AhalfTranspose₂_finset_sum` — the second dual function is an average over the finite set
  `(N/2, N]`, hence additive in its first argument over any finite sum (no hypotheses at all);
* `boundedZ_finset_sum` / `kmtProj_finset_sum` — the projection `Π = kmtProj` is additive on
  *bounded* functions, and a finite sum of bounded functions is bounded;
* `dPiece_eq` (`SivLocal`) — the local dual function `dPiece P N f h i` of the `i`-th block is
  `Ã_N^{**}(f·1_{I_i}, h)`, the `h` of the definition being restricted to the window `hWin P N i`
  which is invisible to `Ã_N^{**}(f·1_{I_i}, ·)`.
-/

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.InverseTheory

namespace Work.KMTAreas.A4Z

/-- **Additivity of `Ã_N^{**}(·,h)` over a finite sum in its first argument.**  The second dual
function is a finite average over `N/2 < n ≤ N`, so this is only the distributivity of the finite
sum over the product; no summability hypothesis is needed. -/
theorem AhalfTranspose₂_finset_sum {ι : Type*} (N : ℕ) (P : Polynomial ℤ) (h : ℤ → ℂ)
    (S : Finset ι) (φ : ι → ℤ → ℂ) :
    AhalfTranspose₂ N P (fun x => ∑ i ∈ S, φ i x) h
      = fun x => ∑ i ∈ S, AhalfTranspose₂ N P (φ i) h x := by
  funext x
  simp only [AhalfTranspose₂]
  rw [show (∑ n ∈ Finset.Ioc (N / 2) N,
        (∑ i ∈ S, φ i (x + (n : ℤ) - P.eval (n : ℤ))) * h (x - P.eval (n : ℤ)))
      = ∑ n ∈ Finset.Ioc (N / 2) N, ∑ i ∈ S,
          φ i (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ)) from
    Finset.sum_congr rfl fun n _ => Finset.sum_mul S _ _]
  rw [Finset.sum_comm, Finset.mul_sum]

/-- **A finite sum of bounded functions is bounded.** -/
theorem boundedZ_finset_sum {ι : Type*} (S : Finset ι) {u : ι → ℤ → ℂ}
    (hu : ∀ i ∈ S, Work.KMTAreas.A5.BoundedZ (u i)) :
    Work.KMTAreas.A5.BoundedZ (fun x => ∑ i ∈ S, u i x) := by
  classical
  induction S using Finset.induction with
  | empty =>
      rw [show (fun x => ∑ i ∈ (∅ : Finset ι), u i x) = 0 from by funext x; simp]
      exact Work.KMTAreas.A5.boundedZ_zero
  | insert a S ha ih =>
      have hua : Work.KMTAreas.A5.BoundedZ (u a) := hu a (Finset.mem_insert_self a S)
      have huS : ∀ i ∈ S, Work.KMTAreas.A5.BoundedZ (u i) :=
        fun i hi => hu i (Finset.mem_insert_of_mem hi)
      have hsum := ih huS
      have hsplit : (fun x => ∑ i ∈ insert a S, u i x)
          = u a + (fun x => ∑ i ∈ S, u i x) := by
        funext x
        rw [Finset.sum_insert ha]
        rfl
      rw [hsplit]
      exact Work.KMTAreas.A5.boundedZ_add hua hsum

/-- **Additivity of the Ionescu--Wainger projection over a finite sum of bounded functions.**
This is the finite-sum form of `Work.KMTAreas.A5.kmtProj_add_bounded`, proved by induction on the
finite set. -/
theorem kmtProj_finset_sum {ι : Type*} (ρ : ℝ) (l : ℕ) (k : ℤ)
    (S : Finset ι) (u : ι → ℤ → ℂ) (hu : ∀ i ∈ S, Work.KMTAreas.A5.BoundedZ (u i)) :
    Work.KMTContract.kmtProj ρ l k (fun x => ∑ i ∈ S, u i x)
      = fun x => ∑ i ∈ S, Work.KMTContract.kmtProj ρ l k (u i) x := by
  classical
  revert u
  induction S using Finset.induction with
  | empty =>
      intro u _
      rw [show (fun x => ∑ i ∈ (∅ : Finset ι), u i x) = 0 from by funext x; simp]
      rw [Work.KMTContract.kmtProj_zero]
      rfl
  | insert a S ha ih =>
      intro u hu
      have hua : Work.KMTAreas.A5.BoundedZ (u a) := hu a (Finset.mem_insert_self a S)
      have huS : ∀ i ∈ S, Work.KMTAreas.A5.BoundedZ (u i) :=
        fun i hi => hu i (Finset.mem_insert_of_mem hi)
      have hbS : Work.KMTAreas.A5.BoundedZ (fun x => ∑ i ∈ S, u i x) :=
        boundedZ_finset_sum S huS
      have hsplit : (fun x => ∑ i ∈ insert a S, u i x)
          = u a + (fun x => ∑ i ∈ S, u i x) := by
        funext x
        rw [Finset.sum_insert ha]
        rfl
      rw [hsplit, Work.KMTAreas.A5.kmtProj_add_bounded ρ l k hua hbS, ih u huS]
      funext x
      rw [Pi.add_apply, Finset.sum_insert ha]

/-- **`T = (1 - Π_{≤l,≤d(l-Log N)}) Ã_N^{**}(·,h)` commutes with the sum over a finite set of
blocks.**  The left-hand side is `T` applied to the function obtained by summing the block pieces
`zPiece (blockLen P N) f i` of `f` over `i ∈ S`; the right-hand side is the sum of the minor-arc
parts `minorPart P ρ N l f h i` of the local dual functions of the blocks. -/
theorem transOp_blockSum (P : Polynomial ℤ) (ρ : ℝ) (N l : ℕ) {f h : ℤ → ℂ}
    (hN : 1 ≤ N) (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hh : ∀ x : ℤ, ‖h x‖ ≤ 1) (S : Finset ℤ) :
    Work.KMTAreas.A4Z.transOp P ρ N l
        (fun x : ℤ => ∑ i ∈ S, Work.KMTAreas.A4Z.zPiece (Work.KMTAreas.A4Z.blockLen P N) f i x) h
      = fun x : ℤ => ∑ i ∈ S, Work.KMTAreas.A4Z.minorPart P ρ N l f h i x := by
  -- Each local dual function is bounded: it is in `ℓ²` by `memLp_ahalfTransposeTwo_of_bdd`.
  have hbdd : ∀ i : ℤ, Work.KMTAreas.A5.BoundedZ (dPiece P N f h i) := fun i => by
    rw [dPiece_eq P N hN i]
    exact Work.KMTAreas.A5.boundedZ_of_memLp (p := (2 : ℝ≥0∞)) (by norm_num)
      (memLp_ahalfTransposeTwo_of_bdd N P hN (zPiece_memLp hf i) hh).1
  -- Step 1: `Ã_N^{**}(∑_i f·1_{I_i}, h) = ∑_i dPiece P N f h i`.
  have hA : AhalfTranspose₂ N P (fun x : ℤ => ∑ i ∈ S, zPiece (blockLen P N) f i x) h
      = fun x : ℤ => ∑ i ∈ S, dPiece P N f h i x := by
    rw [AhalfTranspose₂_finset_sum N P h S (fun i => zPiece (blockLen P N) f i)]
    funext x
    exact Finset.sum_congr rfl fun i _ => by rw [← dPiece_eq P N hN i]
  -- Step 2: the projection is additive on that finite sum.
  have hK : projTwo P ρ N l (fun x : ℤ => ∑ i ∈ S, dPiece P N f h i x)
      = fun x : ℤ => ∑ i ∈ S, projTwo P ρ N l (dPiece P N f h i) x := by
    simp only [projTwo_apply]
    exact kmtProj_finset_sum ρ l
      ((P.natDegree : ℤ) * ((l : ℤ) - Work.Analysis.EndVar.logN N)) S
      (fun i => dPiece P N f h i) (fun i _ => hbdd i)
  -- Step 3: assemble `(1 - Π)(∑_i u_i) = ∑_i (1 - Π)(u_i)`.
  rw [transOp_apply, hA, hK]
  funext x
  simp only [minorPart, Finset.sum_sub_distrib]

end Work.KMTAreas.A4Z
