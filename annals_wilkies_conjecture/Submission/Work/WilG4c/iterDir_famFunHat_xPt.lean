/-
  WilG4c — `iterDir_famFunHat_xPt`: the iterated directional derivative of the family member
  `famFunHat f` at `xPt l x y` along the mixed multiindex `midx p n j M` (BNZ §5.4) is the
  iterated directional derivative of the one-variable function `f l` at `pt x y` along the
  corresponding multiindex `replicate j 0 ++ M.map Fin.succ`.

  The multiindex `midx p n j M` uses only the *last* `n+1` coordinates of `ℝ^{p + (n+1)}`
  (through the embedding `Fin.natAdd p`), i.e. the directions that do not move the parameter
  block.  Along those directions `famFunHat f` is the composition of `f l` with the affine
  inclusion `w ↦ Fin.append l w`, so the claim is the chain rule for the iterated directional
  derivative along an affine map.

  The proof decomposes as follows.

  * `lastIncl p n` is the continuous linear map `v ↦ Fin.append 0 v` (the inclusion of the last
    `n+1` coordinates), written as a finite sum of `smulRight`s of the coordinate projections;
    its two coordinate rules are `lastIncl_apply_castAdd` (vanishing on the parameter block)
    and `lastIncl_apply_natAdd`.
  * `append_eq_lastIncl_add` writes the affine inclusion as the linear part plus a constant, so
    `hasFDerivAt_append_iter`/`fderiv_append` identify its derivative, and `fderiv_append_apply` is
    the chain rule `∂ᵢ (H ∘ (Fin.append l ·)) = ∂_{natAdd p i} H`.
  * `iterDir_append_transport` is the induction on the direction list producing the transport
    identity, and `famFunHat_append`/`midx_eq_map` specialize it to the two functions at hand.
-/
import Mathlib
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.LipDefs
import Submission.Work.WilG4c.Engine
import Submission.Work.WilG4c.IterDirAux

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilG4c

open Work.WilkG4c

/-! ## 1. The inclusion of the last `n+1` coordinates -/

/-- The continuous linear map `v ↦ Fin.append 0 v`, i.e. the inclusion of the last `n+1`
coordinates of `ℝ^{p + (n+1)}` (with the parameter block set to zero).  Written as a finite sum
so that its coordinate rules are immediate. -/
def lastIncl (p n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (p + (n + 1)) → ℝ) :=
  ∑ j : Fin (n + 1),
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) j).smulRight
      (Pi.single (Fin.natAdd p j) (1 : ℝ))

theorem lastIncl_apply_natAdd (p n : ℕ) (v : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    lastIncl p n v (Fin.natAdd p j) = v j := by
  unfold lastIncl
  rw [ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply]
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have hne : Fin.natAdd p b ≠ Fin.natAdd p j := fun h => hb (Fin.natAdd_injective (n + 1) p h)
    rw [Pi.single_eq_of_ne (Ne.symm hne), mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem lastIncl_apply_castAdd (p n : ℕ) (v : Fin (n + 1) → ℝ) (i : Fin p) :
    lastIncl p n v (Fin.castAdd (n + 1) i) = 0 := by
  unfold lastIncl
  rw [ContinuousLinearMap.sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply]
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
  apply Finset.sum_eq_zero
  intro j _
  have hne : Fin.castAdd (n + 1) i ≠ Fin.natAdd p j := by
    intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_natAdd, Fin.val_castAdd] at hv
    have := i.isLt
    omega
  rw [Pi.single_eq_of_ne hne, mul_zero]

/-- `lastIncl` sends the `i`-th standard basis vector of the cube coordinates to the
`(natAdd p i)`-th standard basis vector of the ambient space. -/
theorem lastIncl_single (p n : ℕ) (i : Fin (n + 1)) :
    lastIncl p n (Pi.single i (1 : ℝ)) = Pi.single (Fin.natAdd p i) (1 : ℝ) := by
  funext k
  refine Fin.addCases (fun i' => ?_) (fun j => ?_) k
  · have hne : Fin.castAdd (n + 1) i' ≠ Fin.natAdd p i := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_natAdd, Fin.val_castAdd] at hv
      have := i'.isLt
      omega
    rw [lastIncl_apply_castAdd, Pi.single_eq_of_ne hne]
  · rw [lastIncl_apply_natAdd]
    by_cases h : j = i
    · subst h; simp
    · have hne : Fin.natAdd p j ≠ Fin.natAdd p i := fun hh => h (Fin.natAdd_injective (n + 1) p hh)
      rw [Pi.single_eq_of_ne hne, Pi.single_eq_of_ne h]

/-! ## 2. The affine inclusion `w ↦ Fin.append l w` and its derivative -/

/-- The affine inclusion `w ↦ Fin.append l w` is the linear map `lastIncl p n` plus the
constant `Fin.append l 0`. -/
theorem append_eq_lastIncl_add (p n : ℕ) (l : Fin p → ℝ) (v : Fin (n + 1) → ℝ) :
    Fin.append l v = lastIncl p n v + Fin.append l (0 : Fin (n + 1) → ℝ) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · simp [lastIncl_apply_castAdd, Fin.append_left]
  · simp [lastIncl_apply_natAdd, Fin.append_right]

theorem hasFDerivAt_append_iter (p n : ℕ) (l : Fin p → ℝ) (w : Fin (n + 1) → ℝ) :
    HasFDerivAt (fun w' : Fin (n + 1) → ℝ => Fin.append l w') (lastIncl p n) w := by
  have hfun : (fun w' : Fin (n + 1) → ℝ => Fin.append l w')
      = fun w' => lastIncl p n w' + Fin.append l (0 : Fin (n + 1) → ℝ) := by
    funext w'; exact append_eq_lastIncl_add p n l w'
  rw [hfun]
  exact (lastIncl p n).hasFDerivAt.add_const _

theorem fderiv_append (p n : ℕ) (l : Fin p → ℝ) (w : Fin (n + 1) → ℝ) :
    fderiv ℝ (fun w' : Fin (n + 1) → ℝ => Fin.append l w') w = lastIncl p n :=
  (hasFDerivAt_append_iter p n l w).fderiv

/-- The chain rule for the affine inclusion `Fin.append l`: the directional derivative of
`w ↦ H (Fin.append l w)` in the `i`-th cube direction is the directional derivative of `H` at
`Fin.append l w` in the `(natAdd p i)`-th ambient direction. -/
theorem fderiv_append_apply {p n : ℕ} (H : (Fin (p + (n + 1)) → ℝ) → ℝ) (l : Fin p → ℝ)
    (w : Fin (n + 1) → ℝ) (hH : DifferentiableAt ℝ H (Fin.append l w)) (i : Fin (n + 1)) :
    fderiv ℝ (fun w' => H (Fin.append l w')) w (Pi.single i 1)
      = fderiv ℝ H (Fin.append l w) (Pi.single (Fin.natAdd p i) 1) := by
  have hcomp : fderiv ℝ (fun w' : Fin (n + 1) → ℝ => H (Fin.append l w')) w
      = (fderiv ℝ H (Fin.append l w)).comp (lastIncl p n) := by
    have hf : DifferentiableAt ℝ (fun w' : Fin (n + 1) → ℝ => Fin.append l w') w :=
      (hasFDerivAt_append_iter p n l w).differentiableAt
    have hmain := fderiv_comp (x := w) (f := fun w' : Fin (n + 1) → ℝ => Fin.append l w')
      (g := H) hH hf
    rw [fderiv_append p n l w] at hmain
    exact hmain
  rw [hcomp, ContinuousLinearMap.comp_apply, lastIncl_single]

/-! ## 3. The transport identity for the iterated directional derivative -/

/-- `famFunHat f` composed with the affine inclusion `Fin.append l` is `f l`. -/
theorem famFunHat_append {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (l : Fin p → ℝ) (v : Fin (n + 1) → ℝ) :
    famFunHat f (Fin.append l v) = f l v := by
  simp [famFunHat, Fin.append_left, Fin.append_right]

/-- **Transport of the iterated directional derivative along the affine inclusion.**  For a
function `G` on `ℝ^{p + (n+1)}` that is `C^{|L|}` at `Fin.append l w`, deriving along the
lifted directions `L.map (Fin.natAdd p)` at `Fin.append l w` is the same as deriving `G`
composed with the inclusion, along `L`, at `w`.  Proved by induction on `L`: the two functions
`(iterDir (L'.map (Fin.natAdd p)) G) ∘ (Fin.append l ·)` and `iterDir L' (G ∘ (Fin.append l ·))`
agree on a neighbourhood of `w` (which is where the smoothness hypothesis is used), so their
`fderiv`s coincide, and `fderiv_append_apply` converts the single remaining derivative. -/
theorem iterDir_append_transport {p n : ℕ} (G : (Fin (p + (n + 1)) → ℝ) → ℝ) (l : Fin p → ℝ) :
    ∀ (L : List (Fin (n + 1))) (w : Fin (n + 1) → ℝ),
      ContDiffAt ℝ L.length G (Fin.append l w) →
      iterDir (L.map (Fin.natAdd p)) G (Fin.append l w)
        = iterDir L (fun w' => G (Fin.append l w')) w := by
  intro L
  induction L with
  | nil => intro w _; rfl
  | cons i L' ih =>
    intro w hG
    have hG1 : ContDiffAt ℝ (L'.length + 1) G (Fin.append l w) := hG
    -- `G` is `C^{|L'|}` on a neighbourhood of `Fin.append l w`, hence of `w` after the
    -- inclusion: this is what allows the induction hypothesis to be applied locally.
    have hev : ∀ᶠ w' in 𝓝 w, ContDiffAt ℝ L'.length G (Fin.append l w') := by
      have h1 : ∀ᶠ y in 𝓝 (Fin.append l w), ContDiffAt ℝ (L'.length + 1) G y :=
        hG1.eventually (by simp)
      have h2 : ∀ᶠ y in 𝓝 (Fin.append l w), ContDiffAt ℝ L'.length G y :=
        h1.mono (fun y hy => hy.of_le (by exact_mod_cast Nat.le_succ L'.length))
      exact (hasFDerivAt_append_iter p n l w).continuousAt.tendsto.eventually h2
    have heq : (fun w' => iterDir (L'.map (Fin.natAdd p)) G (Fin.append l w'))
        =ᶠ[𝓝 w] (iterDir L' (fun w'' => G (Fin.append l w''))) := by
      filter_upwards [hev] with w' hw'
      exact ih w' hw'
    have hH : DifferentiableAt ℝ (iterDir (L'.map (Fin.natAdd p)) G) (Fin.append l w) :=
      ((Work.WilG4c.iterDir_contDiffAt G (L'.map (Fin.natAdd p)) 1 (Fin.append l w)) (by
        simpa [List.length_map] using hG1)).differentiableAt one_ne_zero
    simp only [List.map_cons, iterDir_cons, ← heq.fderiv_eq]
    rw [fderiv_append_apply (iterDir (L'.map (Fin.natAdd p)) G) l w hH i]

/-! ## 4. Specialization to `famFunHat` and `midx` -/

/-- `midx p n j M` is the lift through `Fin.natAdd p` of the multiindex
`replicate j 0 ++ M.map Fin.succ` of the cube. -/
theorem midx_eq_map (p n j : ℕ) (M : List (Fin n)) :
    midx p n j M = (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ).map (Fin.natAdd p) := by
  simp only [midx, xDirHat, List.map_append, List.map_replicate, List.map_map]
  rfl

theorem iterDir_famFunHat_xPt {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ)
    (j : ℕ) (M : List (Fin n))
    (h : ContDiffAt ℝ (j + M.length) (Work.WilkG4c.famFunHat f) (Work.WilkG4c.xPt l x y)) :
    Work.WilkG4c.iterDir (Work.WilkG4c.midx p n j M) (Work.WilkG4c.famFunHat f)
        (Work.WilkG4c.xPt l x y)
      = Work.WilkG4c.iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) (f l)
        (Work.WilkG4c.pt x y) := by
  have hlen : (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ).length = j + M.length := by
    simp [List.length_append, List.length_replicate, List.length_map]
  have hsm : ContDiffAt ℝ (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ).length
      (famFunHat f) (Fin.append l (Fin.cons x y)) := by
    rw [hlen]; exact h
  have key := iterDir_append_transport (famFunHat f) l
    (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) (Fin.cons x y) hsm
  rw [midx_eq_map p n j M]
  rw [show xPt l x y = Fin.append l (Fin.cons x y) from rfl, key]
  rw [show (fun w' => famFunHat f (Fin.append l w')) = f l from
    funext (fun w' => famFunHat_append f l w')]
  rfl

end Work.WilG4c
