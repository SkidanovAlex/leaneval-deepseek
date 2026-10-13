/-
# `contDiffOn_plainMixed`

The plain mixed derivative `plainMixed a b g = ∂_z^a ∂_θ^b g` (see `ApproxCC/Defs.lean`)
of a function which is `C^n` on an *open* set `U ⊆ ℝ × ℝ` is `C^{n-(a+b)}` on `U`.

The proof works with the two "partial derivative operators"

* `partialZ G p = deriv (fun z' => G (z', p.2)) p.1`,
* `partialT G p = deriv (fun θ' => G (p.1, θ')) p.2`,

which are related to `partialFDeriv` by the chain rule, so that on the open set `U`
`partialZ G = (fun p => fderiv ℝ G p (1,0))`, and `ContDiffOn.fderiv_of_isOpen` immediately
gives the recursion step `C^{n+1} ⟹ C^n` for the partial derivative.  Iterating gives the
result, using that `partialZ^[a] (partialT^[b] G)` unfolds (definitionally, since `deriv` is a
total function) to `plainMixed a b g`.

One formal trap: the exponent `n - (a + b)` in the statement lives in `WithTop ℕ∞`, so Lean
elaborates it with the *`WithTop` subtraction* rather than `Nat.sub`.  The helper
`withTop_sub_eq_natCast_sub` identifies it with `↑(n - (a + b) : ℕ)`.
-/
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.GalBasis.ApproxCC.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.GalBasis.ApproxCC

/-- The partial derivative in the first variable, as an operator on functions `ℝ × ℝ → ℝ`. -/
def partialZ (G : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => deriv (fun z' => G (z', p.2)) p.1

/-- The partial derivative in the second variable, as an operator on functions `ℝ × ℝ → ℝ`. -/
def partialT (G : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => deriv (fun θ' => G (p.1, θ')) p.2

/-- Iterating `partialZ` computes the plain `z`-iterated derivative of the slices. -/
lemma partialZ_iterate_apply (a : ℕ) (H : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    (partialZ^[a] H) p = iteratedDeriv a (fun z' => H (z', p.2)) p.1 := by
  induction a generalizing p with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply']
      have hfun : (fun z' : ℝ => (partialZ^[a] H) (z', p.2)) =
          (fun z' : ℝ => iteratedDeriv a (fun z'' => H (z'', p.2)) z') := by
        funext z'; exact ih (z', p.2)
      show deriv (fun z' : ℝ => (partialZ^[a] H) (z', p.2)) p.1 = _
      rw [hfun, iteratedDeriv_succ]

/-- Iterating `partialT` computes the plain `θ`-iterated derivative of the slices. -/
lemma partialT_iterate_apply (b : ℕ) (H : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    (partialT^[b] H) p = iteratedDeriv b (fun θ' => H (p.1, θ')) p.2 := by
  induction b generalizing p with
  | zero => simp
  | succ b ih =>
      rw [Function.iterate_succ_apply']
      have hfun : (fun θ' : ℝ => (partialT^[b] H) (p.1, θ')) =
          (fun θ' : ℝ => iteratedDeriv b (fun θ'' => H (p.1, θ'')) θ') := by
        funext θ'; exact ih (p.1, θ')
      show deriv (fun θ' : ℝ => (partialT^[b] H) (p.1, θ')) p.2 = _
      rw [hfun, iteratedDeriv_succ]

/-- On an open set, the partial `z`-derivative is `fderiv G` evaluated at `(1, 0)`; hence it
loses exactly one order of differentiability. -/
lemma contDiffOn_partialZ {G : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) G U) : ContDiffOn ℝ (n : ℕ) (partialZ G) U := by
  have hfd : ContDiffOn ℝ (n : ℕ) (fderiv ℝ G) U := h.fderiv_of_isOpen hU (by norm_num)
  have hcomp : ContDiffOn ℝ (n : ℕ) (fun p => (fderiv ℝ G p) ((1:ℝ), (0:ℝ))) U :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.apply ℝ ℝ ((1:ℝ), (0:ℝ)))).comp_contDiffOn
      hfd
  refine hcomp.congr ?_
  intro p hp
  have hdOn : DifferentiableOn ℝ G U := h.differentiableOn (by norm_num)
  have hd : DifferentiableAt ℝ G p := (hdOn p hp).differentiableAt (hU.mem_nhds hp)
  have hfdp : HasFDerivAt G (fderiv ℝ G p) p := hd.hasFDerivAt
  have hc : HasDerivAt (fun z' : ℝ => ((z', p.2) : ℝ × ℝ)) ((1:ℝ), (0:ℝ)) p.1 := by
    have h1 := (hasFDerivAt_prodMk_left (𝕜:=ℝ) p.1 p.2).hasDerivAt
    simpa using h1
  have hkey := (hfdp.comp_hasDerivAt p.1 hc).deriv
  simpa only [partialZ, Function.comp_def] using hkey

/-- On an open set, the partial `θ`-derivative is `fderiv G` evaluated at `(0, 1)`; hence it
loses exactly one order of differentiability. -/
lemma contDiffOn_partialT {G : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1 : ℕ) G U) : ContDiffOn ℝ (n : ℕ) (partialT G) U := by
  have hfd : ContDiffOn ℝ (n : ℕ) (fderiv ℝ G) U := h.fderiv_of_isOpen hU (by norm_num)
  have hcomp : ContDiffOn ℝ (n : ℕ) (fun p => (fderiv ℝ G p) ((0:ℝ), (1:ℝ))) U :=
    (ContinuousLinearMap.contDiff (ContinuousLinearMap.apply ℝ ℝ ((0:ℝ), (1:ℝ)))).comp_contDiffOn
      hfd
  refine hcomp.congr ?_
  intro p hp
  have hdOn : DifferentiableOn ℝ G U := h.differentiableOn (by norm_num)
  have hd : DifferentiableAt ℝ G p := (hdOn p hp).differentiableAt (hU.mem_nhds hp)
  have hfdp : HasFDerivAt G (fderiv ℝ G p) p := hd.hasFDerivAt
  have hc : HasDerivAt (fun θ' : ℝ => ((p.1, θ') : ℝ × ℝ)) ((0:ℝ), (1:ℝ)) p.2 := by
    have h1 := (hasFDerivAt_prodMk_right (𝕜:=ℝ) p.1 p.2).hasDerivAt
    simpa using h1
  have hkey := (hfdp.comp_hasDerivAt p.2 hc).deriv
  simpa only [partialT, Function.comp_def] using hkey

/-- Iterating the one-order loss for `partialT`. -/
lemma contDiffOn_partialT_iterate {G : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) :
    ∀ (b n : ℕ), b ≤ n → ContDiffOn ℝ (n : ℕ) G U →
      ContDiffOn ℝ (n - b : ℕ) (partialT^[b] G) U := by
  intro b
  induction b with
  | zero => intro n _ h; simpa using h
  | succ b ih =>
      intro n hbn h
      have hb : b ≤ n := Nat.le_of_succ_le hbn
      have h1 : ContDiffOn ℝ (n - b : ℕ) (partialT^[b] G) U := ih n hb h
      have hpos : 1 ≤ n - b := by omega
      have h1' : ContDiffOn ℝ (((n - b - 1) + 1 : ℕ)) (partialT^[b] G) U := by
        rwa [Nat.sub_add_cancel hpos]
      have h2 : ContDiffOn ℝ (n - b - 1 : ℕ) (partialT (partialT^[b] G)) U :=
        contDiffOn_partialT hU h1'
      rw [show (n - (b + 1) : ℕ) = n - b - 1 by omega, Function.iterate_succ_apply']
      exact h2

/-- Iterating the one-order loss for `partialZ`. -/
lemma contDiffOn_partialZ_iterate {G : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) :
    ∀ (a n : ℕ), a ≤ n → ContDiffOn ℝ (n : ℕ) G U →
      ContDiffOn ℝ (n - a : ℕ) (partialZ^[a] G) U := by
  intro a
  induction a with
  | zero => intro n _ h; simpa using h
  | succ a ih =>
      intro n han h
      have ha : a ≤ n := Nat.le_of_succ_le han
      have h1 : ContDiffOn ℝ (n - a : ℕ) (partialZ^[a] G) U := ih n ha h
      have hpos : 1 ≤ n - a := by omega
      have h1' : ContDiffOn ℝ (((n - a - 1) + 1 : ℕ)) (partialZ^[a] G) U := by
        rwa [Nat.sub_add_cancel hpos]
      have h2 : ContDiffOn ℝ (n - a - 1 : ℕ) (partialZ (partialZ^[a] G)) U :=
        contDiffOn_partialZ hU h1'
      rw [show (n - (a + 1) : ℕ) = n - a - 1 by omega, Function.iterate_succ_apply']
      exact h2

/-- `plainMixed a b g` is the iterate `∂_z^a ∂_θ^b` of the uncurried `g`.  Both sides are
total expressions (`deriv` and `iteratedDeriv` are defined everywhere), so the identity needs
no differentiability hypothesis. -/
lemma uncurry_plainMixed_eq (a b : ℕ) (g : ℝ → ℝ → ℝ) :
    Function.uncurry (plainMixed a b g) = (partialZ^[a] (partialT^[b] (Function.uncurry g))) := by
  funext p
  have h1 := partialZ_iterate_apply a (partialT^[b] (Function.uncurry g)) p
  have h2 : (fun z' : ℝ => (partialT^[b] (Function.uncurry g)) (z', p.2)) =
      (fun z' : ℝ => iteratedDeriv b (fun θ' => Function.uncurry g (z', θ')) p.2) := by
    funext z'; exact partialT_iterate_apply b (Function.uncurry g) (z', p.2)
  rw [h1, h2]
  rfl

/-- The `WithTop`-subtraction appearing in the statement of `contDiffOn_plainMixed` coincides
with the coercion of the `Nat` subtraction. -/
lemma withTop_sub_eq_natCast_sub (n a b : ℕ) :
    ((n : WithTop ENat) - ((a : WithTop ENat) + (b : WithTop ENat))) =
      ((n - (a + b) : ℕ) : WithTop ENat) := by
  have hE : ((n : ENat) - ((a : ENat) + (b : ENat)) = ((n - (a + b) : ℕ) : ENat)) := by
    rw [← ENat.natCast_add a b, ← ENat.natCast_sub n (a + b)]
  change (((n : ENat) : WithTop ENat) - (((a : ENat) : WithTop ENat) + ((b : ENat) : WithTop ENat)))
      = (((n - (a + b) : ℕ) : ENat) : WithTop ENat)
  rw [← WithTop.coe_add, ← WithTop.coe_sub, hE]

theorem contDiffOn_plainMixed {g : ℝ → ℝ → ℝ} {n a b : ℕ} (hab : a + b ≤ n) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (h : ContDiffOn ℝ n (Function.uncurry g) U) :
    ContDiffOn ℝ (n - (a + b)) (Function.uncurry (plainMixed a b g)) U := by
  rw [withTop_sub_eq_natCast_sub]
  have hb : b ≤ n := by omega
  have ha : a ≤ n - b := by omega
  have h1 : ContDiffOn ℝ (n - b : ℕ) (partialT^[b] (Function.uncurry g)) U :=
    contDiffOn_partialT_iterate hU b n hb h
  have h2 : ContDiffOn ℝ ((n - b) - a : ℕ) (partialZ^[a] (partialT^[b] (Function.uncurry g))) U :=
    contDiffOn_partialZ_iterate hU a (n - b) ha h1
  have hsub : (n - b) - a = n - (a + b) := by omega
  rw [hsub] at h2
  exact h2.congr (fun p _ => (congrFun (uncurry_plainMixed_eq a b g) p))

end Work.FTS.GalBasis.ApproxCC
