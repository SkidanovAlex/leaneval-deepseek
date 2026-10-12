import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.l2Space
import Submission.Work.BoseBoxFock.KzOpC
import Submission.Work.BoseBoxFock.split_sandwiches
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.split_Q3T_box` — FS `eq:kroelleQ3z` under the ⟨condensate | excited⟩ split

FS's cubic word of `thm:Control3Q` (`eq:kroelleQ3z`, `Work.BoseB7A.TildeData.Q3T`) is

    `Q₃(z) = ℓ⁻³z Σ_{s≠0} Σ_{k∈P_H} f_L(s)Ŵ₁(k)(ã_s† a_{s−k} a_k + a_k† a_{s−k}† ã_s)`,

an operator on the mode lattice `RealFock m` which carries the condensate coordinate
`0`.  Its *spectator* (`c`-number) form — the one `Work.BoseBoxFock.KzOpC` uses, and
the one the `thm:Kafz` symbol comparison of `KAFZ_HONEST_ROUTE.md` §2 consumes — is

    `Q3TC f g F E = ℓ⁻³z Σ_{s≠0} Σ_{k∈P_H} f_L(s)Ŵ₁(k)
        (creOfE (g s) ∘ annOfE (f (s−k)) ∘ annOfE (f k)
         + creOfE (f k) ∘ creOfE (f (s−k)) ∘ annOfE (g s))`,

i.e. the operator obtained from `Q3T` by replacing every honest mode
`annOf m (f k)` / `creOf m (f k)` by its spectator image `annOfE (f k)` /
`creOfE (f k)`, the θ-mode `ã_s` by `annOfE (g s)`, and dropping the condensate
ladder operators (the word carries none: `ã_s`, `a_k` all live off the condensate).

The theorem below records exactly this: under `Work.BoseB4.split`

    `split (T.Q3T E y) = lift (Q3TC f g F E) (split y)`,

with the two split hypotheses `hTa`, `hTaDag` supplying the dictionary for the
abstract θ-modes `T.ta s`, `T.taDag s` (`TildeData` does not pin `ta`; the honest
instance `Work.BoseBoxFock.tildeDataHon` sets `ta s = annOf m (g s)` and discharges
them by `split_annOf`).

## Route

Everything is the *word* `ã_s† a_{s−k} a_k`: `split_annOf`/`split_creOf` transport
`annOf m (f j)`/`creOf m (f j)` to `lift (annOfE (f j))`/`lift (creOfE (f j))`, the
hypotheses `hTa`/`hTaDag` transport the θ-modes, and `lift` is a composition
functor (`Work.BoseB4.lift_comp`), so each pair `(s,k)` transports to a single
`lift` of the composite spectator word (`hterm`).  The double sum is then
reassembled in the *same* order as `Q3TC`'s:
`split_sum_sum_smul` (the dictionary for `Σ_s Σ_k c_{sk} • op_{sk}`, with the
dictionary supplied as a hypothesis), and `lift_sum_sum_smul` (the `lift` of a
double sum of spectator operators is the double sum of the lifts).  The outer
scalar `ℓ⁻³z`, a real number on the lattice and its complex image on the
spectator space, is moved across by `split_map_smul_c` / `lift_smul`.

The one twist forced by the formalisation is that the carrier of the `FockData`
`Work.BoseB4.boxFockData B kmom hkmom m f hf` is `RealFock m` only up to
`rfl`-defeq, so the intermediate goals mix `F.H`-typed operators with
`RealFock m`-typed vectors and are not type-correct at the `implicit` transparency
level used by `rw`'s occurrence check.  The helpers below are therefore stated for
an *abstract* `op : ι → κ → RealFock m →ₗ[ℝ] RealFock m` (no mixing at all, plain
`rw`), and the mixed steps in the main proof are performed with `erw` or with
explicit `congrArg`/`Eq.trans` terms rather than `rw` occurrence rewriting.
-/

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

variable {m : ℕ} [NeZero m]

/-! ## 1. The `lift` dictionary for composites -/

/-- `lift` of a composite, at the level of vectors: `lift A (lift B z) = lift (A ∘ B) z`
(`Work.BoseB4.lift_comp`, applied). -/
private lemma lift_lift_vec {A B : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)}
    (z : FockCore (cfock (Excited m))) :
    lift A (lift B z) = lift (A.comp B) z :=
  (LinearMap.congr_fun (lift_comp A B) z).symm

/-- The dictionary is closed under composition, pointwise. -/
private lemma split_comp_pair {A B : RealFock m →ₗ[ℝ] RealFock m}
    {A' B' : cfock (Excited m) →ₗ[ℂ] cfock (Excited m)}
    (hA : ∀ y : RealFock m, split (A y) = lift A' (split y))
    (hB : ∀ y : RealFock m, split (B y) = lift B' (split y)) (y : RealFock m) :
    split ((A.comp B) y) = lift (A'.comp B') (split y) := by
  rw [LinearMap.comp_apply, hA, hB, lift_lift_vec]

/-! ## 2. The double-sum reassembly, for an abstract word -/

/-- **The dictionary for a weighted double sum** `Σ_s Σ_k c_{sk} • op_{sk}`: if every
word `op_{sk}` transports to `lift (A_{sk})`, then so does the sum, with the real
weights `c_{sk}` becoming their complex images. -/
private lemma split_sum_sum_smul {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (K : Finset κ) (c : ι → κ → ℝ)
    (op : ι → κ → RealFock m →ₗ[ℝ] RealFock m)
    (A : ι → κ → cfock (Excited m) →ₗ[ℂ] cfock (Excited m))
    (hop : ∀ s ∈ S, ∀ k ∈ K, ∀ z : RealFock m, split (op s k z) = lift (A s k) (split z))
    (y : RealFock m) :
    split ((∑ s ∈ S, ∑ k ∈ K, c s k • op s k) y)
      = ∑ s ∈ S, ∑ k ∈ K, (((c s k : ℝ) : ℂ)) • lift (A s k) (split y) := by
  rw [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [LinearMap.smul_apply, Work.BoseB4.split_map_smul_c, hop s hs k hk y]

/-- The `lift` of a weighted double sum of spectator operators is the double sum of
the lifts. -/
private lemma lift_sum_sum_smul {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (K : Finset κ) (c : ι → κ → ℂ)
    (A : ι → κ → cfock (Excited m) →ₗ[ℂ] cfock (Excited m)) :
    lift (∑ s ∈ S, ∑ k ∈ K, c s k • A s k)
      = ∑ s ∈ S, ∑ k ∈ K, c s k • lift (A s k) := by
  rw [Work.BoseB4.lift_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Work.BoseB4.lift_sum]
  exact Finset.sum_congr rfl fun k hk => by rw [Work.BoseB4.lift_smul]

/-! ## 3. The `Q₃` row -/

theorem split_Q3T_box {m : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode] (B : Work.BoseB4.BoxData) {ℓ : ℝ} (kmom : Mode → EuclideanSpace ℝ (Fin 3))
    (hkmom : ∀ i : Mode, kmom (-i) = -kmom i) (f g : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j)
      = Work.BoseB7.ccrKernel ℓ B.hatChiSq B.hatChi (kmom i) (kmom j))
    (hφ : ∀ k : Mode, f k 0 = 0)
    (T : Work.BoseB7A.TildeData (Work.BoseB4.boxFockData B kmom hkmom m f hf))
    (hTa : ∀ s : Mode, s ≠ 0 → ∀ y : Work.BoseB4.RealFock m,
      Work.BoseB4.split (T.ta s y) = Work.BoseB4.lift (Work.BoseBoxFock.annOfE (g s)) (Work.BoseB4.split y))
    (hTaDag : ∀ s : Mode, s ≠ 0 → ∀ y : Work.BoseB4.RealFock m,
      Work.BoseB4.split (T.taDag s y) = Work.BoseB4.lift (Work.BoseBoxFock.creOfE (g s)) (Work.BoseB4.split y))
    (E : Work.BoseB7.Q3Env Mode) :
    ∀ y : Work.BoseB4.RealFock m,
      Work.BoseB4.split (T.Q3T E y)
        = Work.BoseB4.lift (Work.BoseBoxFock.Q3TC f g (Work.BoseB4.boxFockData B kmom hkmom m f hf) E)
            (Work.BoseB4.split y) := by
  classical
  intro y
  -- the χ-mode dictionary, from `hφ`
  have hFa : ∀ (j : Mode) (z : RealFock m),
      split ((boxFockData B kmom hkmom m f hf).a j z) = lift (annOfE (f j)) (split z) :=
    fun j z => split_annOf (f j) (hφ j) z
  have hFc : ∀ (j : Mode) (z : RealFock m),
      split ((boxFockData B kmom hkmom m f hf).aDag j z) = lift (creOfE (f j)) (split z) :=
    fun j z => split_creOf (f j) (hφ j) z
  -- the two halves of the cubic word, one pair `(s,k)` at a time
  have hqtermT : ∀ (s : Mode), s ≠ 0 → ∀ (k : Mode) (z : RealFock m),
      split (T.qtermT s k z)
        = lift ((creOfE (g s)).comp ((annOfE (f (s - k))).comp (annOfE (f k)))) (split z) := by
    intro s hs k z
    have hW : split (((annOf m (f (s - k))) ∘ₗ (annOf m (f k))) z)
        = lift ((annOfE (f (s - k))).comp (annOfE (f k))) (split z) :=
      split_comp_pair (hFa (s - k)) (hFa k) z
    erw [Work.BoseB7A.TildeData.qtermT, LinearMap.comp_apply, hTaDag s hs, hW, lift_lift_vec]
  have hqtermDagT : ∀ (s : Mode), s ≠ 0 → ∀ (k : Mode) (z : RealFock m),
      split (T.qtermDagT s k z)
        = lift ((creOfE (f k)).comp ((creOfE (f (s - k))).comp (annOfE (g s)))) (split z) := by
    intro s hs k z
    have hW : split (((creOf m (f (s - k))) ∘ₗ T.ta s) z)
        = lift ((creOfE (f (s - k))).comp (annOfE (g s))) (split z) :=
      split_comp_pair (hFc (s - k)) (hTa s hs) z
    erw [Work.BoseB7A.TildeData.qtermDagT, LinearMap.comp_apply, hFc k, hW, lift_lift_vec]
  have hterm : ∀ (s : Mode), s ≠ 0 → ∀ (k : Mode) (z : RealFock m),
      split ((T.qtermT s k + T.qtermDagT s k) z)
        = lift ((creOfE (g s)).comp ((annOfE (f (s - k))).comp (annOfE (f k)))
                + (creOfE (f k)).comp ((creOfE (f (s - k))).comp (annOfE (g s)))) (split z) := by
    intro s hs k z
    calc split ((T.qtermT s k + T.qtermDagT s k) z)
        = split (T.qtermT s k z) + split (T.qtermDagT s k z) := by
            erw [LinearMap.add_apply, map_add]
      _ = lift ((creOfE (g s)).comp ((annOfE (f (s - k))).comp (annOfE (f k)))) (split z)
            + lift ((creOfE (f k)).comp ((creOfE (f (s - k))).comp (annOfE (g s)))) (split z) := by
            erw [hqtermT s hs k z, hqtermDagT s hs k z]
      _ = lift ((creOfE (g s)).comp ((annOfE (f (s - k))).comp (annOfE (f k)))
                + (creOfE (f k)).comp ((creOfE (f (s - k))).comp (annOfE (g s)))) (split z) := by
            erw [← LinearMap.add_apply, ← lift_add]
  -- the `s`-sum runs over the excited modes, hence `s ≠ 0`
  have hs0 : ∀ s ∈ Work.BoseB7.excited Mode, s ≠ 0 := by
    intro s hs
    simpa only [Work.BoseB7.excited, Finset.mem_erase, Finset.mem_univ, and_true] using hs
  -- the double sum of the words
  have hS : split (((∑ s ∈ Work.BoseB7.excited Mode,
        ∑ k ∈ (boxFockData B kmom hkmom m f hf).PHset E,
        (E.fL s * E.W1 k) • (T.qtermT s k + T.qtermDagT s k))) y)
      = ∑ s ∈ Work.BoseB7.excited Mode,
          ∑ k ∈ (boxFockData B kmom hkmom m f hf).PHset E,
          (((E.fL s * E.W1 k) : ℝ) : ℂ) •
            lift ((creOfE (g s)).comp ((annOfE (f (s - k))).comp (annOfE (f k)))
              + (creOfE (f k)).comp ((creOfE (f (s - k))).comp (annOfE (g s)))) (split y) :=
    split_sum_sum_smul (S := Work.BoseB7.excited Mode)
      (K := (boxFockData B kmom hkmom m f hf).PHset E)
      (c := fun s k => E.fL s * E.W1 k)
      (op := fun s k => T.qtermT s k + T.qtermDagT s k)
      (A := fun s k => (creOfE (g s)).comp ((annOfE (f (s - k))).comp (annOfE (f k)))
              + (creOfE (f k)).comp ((creOfE (f (s - k))).comp (annOfE (g s))))
      (hop := fun s hs k hk z => hterm s (hs0 s hs) k z) y
  -- the `lift` of the summed spectator operator, split into the summed lifts
  have hS' : lift (∑ s ∈ Work.BoseB7.excited Mode,
          ∑ k ∈ (boxFockData B kmom hkmom m f hf).PHset E,
          (((E.fL s * E.W1 k) : ℝ) : ℂ) •
            ((creOfE (g s)).comp ((annOfE (f (s - k))).comp (annOfE (f k)))
              + (creOfE (f k)).comp ((creOfE (f (s - k))).comp (annOfE (g s))))) (split y)
      = ∑ s ∈ Work.BoseB7.excited Mode,
          ∑ k ∈ (boxFockData B kmom hkmom m f hf).PHset E,
          (((E.fL s * E.W1 k) : ℝ) : ℂ) •
            lift ((creOfE (g s)).comp ((annOfE (f (s - k))).comp (annOfE (f k)))
              + (creOfE (f k)).comp ((creOfE (f (s - k))).comp (annOfE (g s)))) (split y) := by
    rw [lift_sum_sum_smul]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  -- the two outer scalars `ℓ⁻³z`
  have hfirst : split (T.Q3T E y)
      = (((E.z / E.ell ^ 3 : ℝ) : ℂ)) • split (((∑ s ∈ Work.BoseB7.excited Mode,
        ∑ k ∈ (boxFockData B kmom hkmom m f hf).PHset E,
        (E.fL s * E.W1 k) • (T.qtermT s k + T.qtermDagT s k))) y) := by
    erw [Work.BoseB7A.TildeData.Q3T, LinearMap.smul_apply, Work.BoseB4.split_map_smul_c]
  have hlast : lift (Work.BoseBoxFock.Q3TC f g (Work.BoseB4.boxFockData B kmom hkmom m f hf) E)
        (split y)
      = (((E.z / E.ell ^ 3 : ℝ) : ℂ)) • lift (∑ s ∈ Work.BoseB7.excited Mode,
          ∑ k ∈ (boxFockData B kmom hkmom m f hf).PHset E,
          (((E.fL s * E.W1 k) : ℝ) : ℂ) •
            ((creOfE (g s)).comp ((annOfE (f (s - k))).comp (annOfE (f k)))
              + (creOfE (f k)).comp ((creOfE (f (s - k))).comp (annOfE (g s))))) (split y) := by
    rw [Work.BoseBoxFock.Q3TC, Work.BoseB4.lift_smul, LinearMap.smul_apply]
  exact (hfirst.trans (congrArg (fun t => (((E.z / E.ell ^ 3 : ℝ) : ℂ)) • t)
    (hS.trans hS'.symm))).trans hlast.symm

end Work.BoseBoxFock
