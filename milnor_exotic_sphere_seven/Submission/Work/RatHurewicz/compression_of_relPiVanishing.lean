import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.RatHurewicz.CompressionDefs
import Submission.Work.RatHurewicz.CompressionGeometry
import Submission.Work.RatHurewicz.pinchedMap_nullHomotopic
import Submission.Work.RatHurewicz.Triad.Convert

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

/-- The clamping map fixes `0`. -/
theorem clampI_zero' : clampI 0 = (0 : unitInterval) := by
  rw [clampI_of_mem (show (0 : ℝ) ≤ 0 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)]
  exact Subtype.ext rfl

/-- The clamping map fixes `1`. -/
theorem clampI_one' : clampI 1 = (1 : unitInterval) := by
  rw [clampI_of_mem (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 1 by norm_num)]
  exact Subtype.ext rfl

/-- **The compression property from the vanishing of the relative groups** (the equivalence
(3) ⟺ (1) of tom Dieck, *Algebraic Topology*, (6.7.5)).

Let `A ⊆ Y` and `n : ℕ`.  Assume
* every point of `Y` is joined by a path to a point of `A` (the `0`-connectivity of the pair, the
  case `q = 0` of (6.7.5)(1)), and
* for every base point `a ∈ A` and every `k ≤ n`, the `k`-th homotopy group of the homotopy fibre
  of `setIncl A : ↥A → Y` at `a` is trivial — equivalently, in the classical indexing, the relative
  groups `π_q(Y,A,a)` vanish for `1 ≤ q ≤ n+1` and every `a ∈ A`.

Then the pair `(Y, A)` has the **compression property** in all dimensions `d ≤ n+1`: every map of
pairs `(Iᵈ, ∂Iᵈ) → (Y, A)` is homotopic, relative to the boundary, to a map into `A`
(`CompressRel Y A d`, `Submission/Work/RatHurewicz/ExcisionSetup.lean`).

Route, following the proofs of (6.7.2) and (6.7.3).  (The previous draft of this statement asked
only for the vanishing at a *single* base point `a₀`, which is too weak: with
`Y = (-2,1) ∪ (2,7)`, `A = (-1,0) ∪ (2,3) ∪ (4,5)` and `a₀ = -1/2` the fibre at `a₀` is
contractible, yet a path in `Y` joining the components `(2,3)` and `(4,5)` of `A` cannot be
deformed relative to its endpoints into `A`.  Hence the hypothesis is stated at every base point,
as in (6.7.5)(3).)

1. *Reduction to the pinched model.*  `RelHomotopyGroup (setIncl A) a k := HomotopyGroup (Fin k)
   (homotopyFibre (setIncl A) a) …` is `π_k` of the homotopy fibre of `A ↪ Y` at `a`, which is the
   classical `π_{k+1}(Y,A,a)` (the "pinched" model, (6.1.3)(4)): a based `k`-cube in the fibre
   unwraps to a map of triples `(I^{k+1}, ∂I^{k+1}, J^k) → (Y,A,a)` with `J^k = ∂I^k × I ∪ I^k ×
   {0} ↦ {a}` and the top face `I^k × {1}` mapping into `A`.
2. *Making a map of pairs pinched.*  Given `f : (I^d, ∂I^d) → (Y,A)`, use that `J^{d-1}` is
   contractible to homotope (through maps of pairs, using that `J^{d-1} ⊆ ∂I^d` and `∂I^d ⊆ I^d`
   are cofibrations) the restriction `f|J^{d-1}` to the constant map at some `a ∈ A`; this gives a
   map of triples.  The vanishing of the homotopy groups of the fibre then makes it null-homotopic
   as a map of triples, i.e. `f` is homotopic as a map of pairs to a constant map, and in
   particular to a map into `A` — this is (6.7.3) (1) ⟹ (2).
3. *Relative to the boundary.*  Upgrade a homotopy "through maps of pairs" to one relative to the
   boundary by the explicit reparametrisation of (6.7.2): if `G_t : (I^d, ∂I^d) → (Y,A)` is a
   homotopy from `f` to a map `k` into `A`, then with `α(x,t) := max(2‖x‖, 2 - t)` the map
   `H = G ∘ Ψ`, `Ψ(x,t) := (2α(x,t)^{-1} x, 2 - α(x,t))`, is a homotopy relative to `∂I^d` from
   `f` to a map into `A`.
   (The `0`-dimensional case `d = 0` is `CompressRel Y A 0`, which is exactly the `0`-connectivity
   hypothesis.) -/
theorem compression_of_relPiVanishing {Y : Type} [TopologicalSpace Y] {A : Set Y} (n : ℕ)
    (hconn : ∀ y : Y, ∃ a : ↥A, Nonempty (Path y a))
    (hvan : ∀ a : ↥A, ∀ k, k ≤ n → Subsingleton (RelHomotopyGroup (setIncl A) a k)) :
    ∀ d, d ≤ n + 1 → CompressRel Y A d := by
  classical
  intro d hd
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · -- the zero-dimensional case is exactly the `0`-connectivity hypothesis
    subst h0
    intro f hf
    obtain ⟨a, ⟨γ⟩⟩ := hconn (f (fun i : Fin 0 => i.elim0))
    refine ⟨⟨fun p : ICube 0 × I => γ p.2, γ.continuous.comp continuous_snd⟩, ?_, ?_, ?_⟩
    · intro x
      show γ (0 : I) = f x
      rw [show x = (fun i : Fin 0 => i.elim0) from funext (fun i => i.elim0)]
      exact γ.source'
    · intro x hx t
      obtain ⟨i, -⟩ := hx
      exact i.elim0
    · intro x
      show γ.toFun (1 : I) ∈ A
      rw [γ.target']
      exact a.2
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
    intro f hf
    -- step 1: homotope `f` through maps of pairs to a map pinched at `f (pinchBase e)`
    obtain ⟨H1, hH10, hH1A, hH1pinch⟩ := exists_pinch e f hf
    -- step 2: the vanishing of the relative group makes the pinched map null-homotopic
    have hvan' : Subsingleton (RelHomotopyGroup (setIncl A)
        ⟨f (pinchBase e), hf _ (pinchBase_mem_boundary e)⟩ e) :=
      hvan _ e (by omega)
    obtain ⟨L, hL0, hLA, hL1⟩ := pinchedMap_nullHomotopic e
      ⟨f (pinchBase e), hf _ (pinchBase_mem_boundary e)⟩ hvan'
      ⟨fun x => H1 (x, 1), by fun_prop⟩ hH1pinch (fun x hx => hH1A x hx 1)
    -- step 3: concatenate the two homotopies through maps of pairs
    set Gfun : ICube (e + 1) × I → Y := fun p =>
      if (2 : ℝ) * (p.2 : ℝ) ≤ 1 then H1 (p.1, clampI (2 * (p.2 : ℝ)))
      else L (p.1, clampI (2 * (p.2 : ℝ) - 1)) with Gfun_def
    have hGcont : Continuous Gfun := by
      rw [Gfun_def]
      refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
      · exact H1.continuous.comp (continuous_fst.prodMk (continuous_clampI.comp (by fun_prop)))
      · exact L.continuous.comp (continuous_fst.prodMk (continuous_clampI.comp (by fun_prop)))
      · exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
      · exact continuous_const
      · intro p hp
        have h1 : clampI (2 * (p.2 : ℝ)) = (1 : I) := by rw [hp, clampI_one']
        have h2 : clampI (2 * (p.2 : ℝ) - 1) = (0 : I) := by
          have h2' : 2 * (p.2 : ℝ) - 1 = 0 := by rw [hp]; norm_num
          rw [h2', clampI_zero']
        rw [h1, h2]
        exact (hL0 p.1).symm
    have hGle : ∀ p : ICube (e + 1) × I, (2 : ℝ) * (p.2 : ℝ) ≤ 1 →
        Gfun p = H1 (p.1, clampI (2 * (p.2 : ℝ))) := by
      intro p h
      rw [Gfun_def]
      exact if_pos h
    have hGgt : ∀ p : ICube (e + 1) × I, ¬ (2 : ℝ) * (p.2 : ℝ) ≤ 1 →
        Gfun p = L (p.1, clampI (2 * (p.2 : ℝ) - 1)) := by
      intro p h
      rw [Gfun_def]
      exact if_neg h
    have hG0 : ∀ x : ICube (e + 1), Gfun (x, 0) = f x := by
      intro x
      rw [hGle (x, 0) (by norm_num),
        show (2 : ℝ) * (((0 : I) : ℝ)) = 0 by norm_num, clampI_zero']
      exact hH10 x
    have hGbd : ∀ x, x ∈ Cube.boundary (Fin (e + 1)) → ∀ t : I, Gfun (x, t) ∈ A := by
      intro x hx t
      by_cases h : (2 : ℝ) * (t : ℝ) ≤ 1
      · rw [hGle (x, t) h]
        exact hH1A x hx _
      · rw [hGgt (x, t) h]
        exact hLA x hx _
    have hG1 : ∀ x : ICube (e + 1), Gfun (x, 1) ∈ A := by
      intro x
      rw [hGgt (x, 1) (by norm_num),
        show (2 : ℝ) * (((1 : I) : ℝ)) - 1 = 1 by norm_num, clampI_one']
      rw [hL1 x]
      exact hf _ (pinchBase_mem_boundary e)
    -- step 4: make the homotopy relative to the boundary (tom Dieck (6.7.2))
    exact Triad.compressRel_of_homotopyPairs f ⟨Gfun, hGcont⟩ hG0 hGbd hG1

end

end Work.RatHurewicz
