/-
  WilG4c / `JointC1LocMem` — the *joint* `C¹`-locus of a family member is `Ω`-definable.

  ## What is proved

  For a family `g : ℝ^m × ℝ^N → ℝ` whose graph `famGraph g ⊆ ℝ^{m+N+1}` is an `Ω`-set, the
  set of points `z : ℝ^{m+N}` at which the *joint* function

      `famFun g z = g (z_0,…,z_{m-1}) (z_m,…,z_{m+N-1})`

  is `C¹` is again an `Ω`-set, with a format independent of the degree parameter `D` and a
  degree polynomial in `D`.

  ## How

  The predicate `ContDiffAt ℝ 1` is replaced by the equivalent (`c1RealPred_slice`, proved)
  `ε`-`δ` predicate `C1Pred`, which is a first-order formula over the graph.  The shape realising
  it is `c1P` (`SliceC1Shape`) used with `P = 0` parameters and `M = m+N` cube coordinates: with
  no parameter coordinates *all* `m+N` directions vary, so `C1Exp 0 (m+N) (graphOf F) w` is
  exactly `C1Pred` of the function whose graph is the `Ω`-set — this is
  `C1Exp_zero_iff_C1Pred` below.

  The single technical annoyance is that `c1P` with `P = 0` lives in the ambient dimension
  `0 + (m+N)` (which is *not* definitionally `m+N`), whereas the target set lives in
  `Fin (m+N)`.  Three index bridges handle this:

  * the graph of the reindexed function `u ↦ f (u ∘ Fin.natAdd 0)` is the transport of the graph
    of `f` along `M + 1 = 0 + M + 1` (`graphOf_reindex`), so that `Work.WilG0.Omega_cast`
    produces the right `Ω`-membership: `C1Exp_mem_Omega` is applied in dimension `0 + (m+N) + 1`;
  * the `Ω`-set obtained in dimension `0 + (m+N)` is pulled back to dimension `m+N` along the
    substitution `Fin.cast (Nat.zero_add ·)` with `Work.WilG0.substSet_mem`;
  * read through that substitution, the point `w = z ∘ Fin.cast (Nat.zero_add ·)` satisfies
    `w (Fin.natAdd 0 j) = z j` (`fin_cast_natAdd_zero`), so the two `Fin M`-indexed `ℓ²` balls
    agree *literally*: no sum reindexing is ever needed.

  The shape-extraction step (`C1Exp_mem_Omega`) is the same computation as the fibre case
  `SliceC1_mem_m`, and is proved in the sibling module `Submission.Work.WilG4c.C1Exp_mem_Omega`;
  `hcd` is passed through unchanged (neither file's argument needs `SharpCD`).

  Everything here is `sorry`-free.
-/
import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.SliceC1Shape
import Submission.Work.WilG4c.SliceC1Real
import Submission.Work.WilG4c.c1RealFD
import Submission.Work.WilG4c.C1Exp_mem_Omega

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The graph of a function: eliminating the value coordinate -/

/-- A graph point is determined by its value: `∃ t, (u,t) ∈ graphOf F ∧ Ψ t ↔ Ψ (F u)`. -/
private theorem exists_snoc_graphOf {n : ℕ} (F : (Fin n → ℝ) → ℝ) (u : Fin n → ℝ)
    (Ψ : ℝ → Prop) :
    (∃ t : ℝ, Fin.snoc u t ∈ WilkiesDesign.graphOf F ∧ Ψ t) ↔ Ψ (F u) := by
  constructor
  · rintro ⟨t, hmem, hΨ⟩
    have ht : t = F u := by simpa [WilkiesDesign.graphOf] using hmem
    rw [← ht]
    exact hΨ
  · rintro h
    exact ⟨F u, by simp [WilkiesDesign.graphOf], h⟩

/-! ## 2. `C1Exp` with no parameters is `C1Pred` -/

/-- With no parameter coordinates (`P = 0`, so *all* `M` directions vary) the expansion
`C1Exp 0 M` of the `ε`-`δ` `C¹`-condition over a graph is exactly the localised predicate
`C1Pred` of the function whose graph it is.  It is stated with the `Fin M`-indexed point
`w ∘ Fin.natAdd 0` so that the two sides carry the *same* `Fin M`-indexed `ℓ²` balls. -/
theorem C1Exp_zero_iff_C1Pred {M : ℕ} (F : (Fin (0 + M) → ℝ) → ℝ) (w : Fin (0 + M) → ℝ) :
    C1Exp 0 M (WilkiesDesign.graphOf F) w ↔
      C1Pred (fun u : Fin M → ℝ => F (Fin.append (w ∘ (fun i : Fin 0 => Fin.castAdd M i)) u))
        (fun j : Fin M => w (Fin.natAdd 0 j)) := by
  simp only [C1Exp, C1Pred, HasFDerivEps, exists_snoc_graphOf]

/-! ## 3. Reindexing `Fin M` by `Fin (0 + M)` -/

/-- Transport of `Ω`-membership along an equality of ambient dimensions. -/
private theorem mem_transport {a b : ℕ} (h : a = b) (A : Set (Fin a → ℝ)) (v : Fin b → ℝ) :
    v ∈ (h ▸ A) ↔ (v ∘ Fin.cast h) ∈ A := by
  cases h
  simp

/-- The graph of the reindexed function `u ↦ f (u ∘ Fin.natAdd 0)` on `Fin (0+M)` is the
transport of the graph of `f` along `M + 1 = 0 + M + 1`. -/
private theorem graphOf_reindex (M : ℕ) (f : (Fin M → ℝ) → ℝ) (h : M + 1 = 0 + M + 1)
    (v : Fin (0 + M + 1) → ℝ) :
    v ∈ WilkiesDesign.graphOf
        (fun u : Fin (0 + M) → ℝ => f (fun j : Fin M => u (Fin.natAdd 0 j)))
      ↔ (v ∘ Fin.cast h) ∈ WilkiesDesign.graphOf f := by
  have h1 : Fin.cast h (Fin.last M) = Fin.last (0 + M) := Fin.ext (by simp)
  have h2 : ∀ j : Fin M, Fin.cast h (Fin.castSucc j) = Fin.castSucc (Fin.natAdd 0 j) :=
    fun j => Fin.ext (by simp)
  simp only [WilkiesDesign.graphOf, Set.mem_ofPred_eq, Function.comp_apply, Fin.init_def]
  rw [h1]
  simp only [h2]

/-- Reading a point of `Fin M` back through `Fin.cast (Nat.zero_add M)`. -/
private theorem fin_cast_natAdd_zero (M : ℕ) (h : 0 + M = M) (j : Fin M) :
    Fin.cast h (Fin.natAdd 0 j) = j :=
  Fin.ext (by simp)

/-! ## 4. The joint `C¹`-locus of a function with an `Ω`-graph -/

/-- **The `Ω`-definability of the joint `C¹`-locus.** If the graph of `f : ℝ^M → ℝ` is an
`Ω`-set of format `F0` and degree `D`, then `{z | ContDiffAt ℝ 1 f z}` is an `Ω`-set with format
independent of `D` and degree polynomial in `D`. -/
theorem famContDiffAt_mem (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (M F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (f : (Fin M → ℝ) → ℝ),
      WilkiesDesign.graphOf f ∈ S.Ω F0 D (M + 1) →
      {z : Fin M → ℝ | ContDiffAt ℝ 1 f z} ∈ S.Ω a (b.eval D) M := by
  obtain ⟨a0, b0, hA⟩ := C1Exp_mem_Omega (S := S) hcd F0 0 M
  refine ⟨max (a0 + M) (M + (0 + M)) + 1 + (0 + M) + M, b0 + Polynomial.C 2, ?_⟩
  intro D f hf
  -- the reindexed function on `Fin (0 + M)`
  let F : (Fin (0 + M) → ℝ) → ℝ := fun u => f (fun j : Fin M => u (Fin.natAdd 0 j))
  have hd : M + 1 = 0 + M + 1 := by omega
  -- its graph is the transported graph of `f`, hence an `Ω`-set in dimension `0 + M + 1`
  have hgraph : WilkiesDesign.graphOf F = (hd ▸ WilkiesDesign.graphOf f) := by
    ext v
    rw [mem_transport]
    exact graphOf_reindex M f hd v
  have hG : WilkiesDesign.graphOf F ∈ S.Ω F0 D (0 + M + 1) := by
    rw [hgraph]
    exact Work.WilG0.Omega_cast hd hf
  -- the realised `C1Exp`-set, in the ambient dimension `0 + M`
  have hzero : 0 + M = M := Nat.zero_add M
  have hres := hA D (WilkiesDesign.graphOf F) hG
  -- pull it back to dimension `M` along `Fin.cast (Nat.zero_add M)`
  have hsub := Work.WilG0.substSet_mem (S := S) hres M (Fin.cast hzero)
  have hset : {x : Fin M → ℝ | x ∘ Fin.cast hzero ∈
        {z : Fin (0 + M) → ℝ | C1Exp 0 M (WilkiesDesign.graphOf F) z}}
      = {z : Fin M → ℝ | ContDiffAt ℝ 1 f z} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    rw [C1Exp_zero_iff_C1Pred]
    have hfun : (fun u : Fin M → ℝ => F (Fin.append ((z ∘ Fin.cast hzero) ∘
        (fun i : Fin 0 => Fin.castAdd M i)) u)) = f := by
      funext u
      simp only [F, Fin.append_right]
    have hpt : (fun j : Fin M => (z ∘ Fin.cast hzero) (Fin.natAdd 0 j)) = z := by
      funext j
      simp only [Function.comp_apply]
      rw [fin_cast_natAdd_zero M hzero j]
    rw [hfun, hpt]
    exact c1RealPred_slice f z
  rw [hset] at hsub
  have hb : (b0 + Polynomial.C 2).eval D = b0.eval D + 2 := by simp
  rw [hb]
  exact hsub

/-! ## 5. The target -/

/-- The joint `C¹`-locus of a family member is `Ω`-definable: the predicate
`ContDiffAt ℝ 1 (famFun g) z` is a first-order formula over the graph of `g` (the `ε`-`δ`
characterisation `C1Pred`, realised by the shape `c1P` with `P = 0`, `M = m+N`), so the set
`{z | ContDiffAt ℝ 1 (famFun g) z}` is an `Ω`-set with format independent of `D` and degree
polynomial in `D`.  (Compare `Work.WilG4c.SliceC1_mem_m`, which does the *fibre* locus with
`P = p`; that file's `hder : SharpDeriv` argument is in fact unused, so only `hcd` is needed.) -/
theorem JointC1LocMem (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (m N F0 : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (g : (Fin m → ℝ) → (Fin N → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph g ∈ S.Ω F0 D (m + N + 1) →
      {z : Fin (m + N) → ℝ | ContDiffAt ℝ 1 (Work.WilG4c.famFun g) z}
        ∈ S.Ω a (b.eval D) (m + N) := by
  obtain ⟨a, b, h⟩ := famContDiffAt_mem S hcd (m + N) F0
  refine ⟨a, b, ?_⟩
  intro D g hfam
  exact h D (famFun g) (by rwa [graphOf_famFun])

end Work.WilG4c
